%% Regression tests for the published advisories against esaml 4.6.0.
%% Each test drives a public entry point, so the same file runs against the
%% released code (where it must fail) and against the fixed code.
-module(esaml_security_tests).

-include_lib("eunit/include/eunit.hrl").
-include_lib("xmerl/include/xmerl.hrl").
-include_lib("public_key/include/public_key.hrl").
-include("esaml.hrl").

-define(DEFLATE, <<"urn:oasis:names:tc:SAML:2.0:bindings:URL-Encoding:DEFLATE">>).
-define(SAMLP, "urn:oasis:names:tc:SAML:2.0:protocol").
-define(SAML, "urn:oasis:names:tc:SAML:2.0:assertion").
-define(CONSUME, "https://sp.example.test/consume").
-define(ENTITY, "https://sp.example.test").

%% ---------------------------------------------------------------------------
%% CVE-2026-28809: XML external entities and external DTDs
%% ---------------------------------------------------------------------------

xxe_external_dtd_is_refused_test() ->
    with_dtd(fun(Path) ->
        Doc = ["<!DOCTYPE samlp:Response SYSTEM \"", Path, "\">", response("")],
        assert_refused(b64(Doc)),
        assert_refused(?DEFLATE, deflated(Doc))
    end).

xxe_external_entity_is_refused_test() ->
    with_dtd(fun(Path) ->
        Doc = ["<!DOCTYPE samlp:Response [<!ENTITY x SYSTEM \"file://", Path, "\">]>",
               response("<samlp:StatusMessage>&x;</samlp:StatusMessage>")],
        assert_refused(b64(Doc))
    end).

xxe_internal_entity_is_refused_test() ->
    Doc = ["<!DOCTYPE samlp:Response [<!ENTITY a \"aaaaaaaaaa\">]>", response("")],
    assert_refused(b64(Doc)).

xxe_utf16_doctype_is_refused_test() ->
    Doc = iolist_to_binary(["<!DOCTYPE samlp:Response SYSTEM \"/nonexistent.dtd\">", response("")]),
    Utf16 = unicode:characters_to_binary(Doc, utf8, {utf16, big}),
    assert_refused(base64:encode(<<16#FE, 16#FF, Utf16/binary>>)).

xxe_in_encrypted_assertion_is_refused_test_() ->
    {timeout, 60, fun() ->
        with_dtd(fun(Path) ->
            Key = rsa_key(),
            SP = unsigned_sp(Key),
            Clean = encrypted_response(assertion(#{}), Key),
            ?assertMatch({ok, #esaml_assertion{}},
                         esaml_sp:validate_assertion(decode(b64(Clean)), SP)),
            Plain = ["<!DOCTYPE saml:Assertion SYSTEM \"", Path, "\">", assertion(#{})],
            Dirty = encrypted_response(Plain, Key),
            ?assertMatch({error, _}, esaml_sp:validate_assertion(decode(b64(Dirty)), SP))
        end)
    end}.

xxe_in_fetched_metadata_is_not_expanded_test() ->
    %% Metadata comes from a configured URL. The cache holds the decoded record,
    %% so this asserts the parser options through the same scan helper.
    Doc = <<"<!DOCTYPE r [<!ENTITY x SYSTEM \"file:///etc/hosts\">]><r>&x;</r>">>,
    assert_refused(base64:encode(Doc)).

%% ---------------------------------------------------------------------------
%% CVE-2026-93471: unbounded decompression
%% ---------------------------------------------------------------------------

inflate_bomb_deflate_binding_is_refused_test_() ->
    {timeout, 120, fun() ->
        Bomb = deflated(response(["<samlp:StatusMessage>", binary:copy(<<"a">>, 2 * 1024 * 1024),
                                  "</samlp:StatusMessage>"])),
        ?assert(byte_size(Bomb) < 16 * 1024),
        assert_refused(?DEFLATE, Bomb)
    end}.

inflate_bomb_default_binding_is_refused_test_() ->
    {timeout, 120, fun() ->
        Bomb = deflated(response(["<samlp:StatusMessage>", binary:copy(<<"a">>, 2 * 1024 * 1024),
                                  "</samlp:StatusMessage>"])),
        assert_refused(Bomb)
    end}.

inflate_stops_at_the_limit_test_() ->
    {timeout, 120, fun() ->
        %% 2 MB of output followed by corrupt data. An unbounded inflate reads to
        %% the corrupt bytes; a bounded one stops long before them.
        Z = zlib:open(),
        ok = zlib:deflateInit(Z, default, deflated, -15, 8, default),
        Head = iolist_to_binary(zlib:deflate(Z, binary:copy(<<"a">>, 2 * 1024 * 1024), sync)),
        ok = zlib:close(Z),
        Broken = base64:encode(<<Head/binary, 16#FF, 16#FF>>),
        ?assertError({saml_payload_refused, payload_too_large},
                     esaml_binding:decode_response(?DEFLATE, Broken)),
        ?assertError({saml_payload_refused, payload_too_large},
                     esaml_binding:decode_response(<<>>, Broken))
    end}.

oversize_plain_payload_is_refused_test_() ->
    {timeout, 120, fun() ->
        Doc = response(["<samlp:StatusMessage>", binary:copy(<<"a">>, 600 * 1024),
                        "</samlp:StatusMessage>"]),
        assert_refused(b64(Doc))
    end}.

payload_under_the_limit_is_accepted_test_() ->
    {timeout, 60, fun() ->
        Doc = response(["<samlp:StatusMessage>", binary:copy(<<"a">>, 200 * 1024),
                        "</samlp:StatusMessage>"]),
        ?assertMatch(#xmlElement{name = 'samlp:Response'}, decode(b64(Doc))),
        ?assertMatch(#xmlElement{name = 'samlp:Response'},
                     esaml_binding:decode_response(?DEFLATE, deflated(Doc)))
    end}.

%% ---------------------------------------------------------------------------
%% CVE-2026-105270: atoms from XML names
%% ---------------------------------------------------------------------------

fresh_element_and_attribute_names_make_no_atoms_test() ->
    Names = [fresh() || _ <- lists:seq(1, 500)],
    Body = [["<", N, " a", N, "=\"x\"/>"] || N <- Names],
    try_decode(b64(response(["<samlp:Extensions>", Body, "</samlp:Extensions>"]))),
    lists:foreach(fun(N) -> assert_no_atom(N), assert_no_atom("a" ++ N) end, Names).

fresh_namespace_uri_makes_no_atom_test() ->
    A = "urn:x:" ++ fresh(),
    B = "urn:x:" ++ fresh(),
    try_decode(b64(response(["<samlp:Extensions xmlns=\"", A, "\"/>"]))),
    try_decode(b64(response(["<samlp:Extensions xmlns:ds=\"", B, "\"/>"]))),
    assert_no_atom(A),
    assert_no_atom(B).

fresh_prefix_makes_no_atom_test() ->
    P = fresh(),
    try_decode(b64(response(["<", P, ":Status xmlns:", P, "=\"urn:oasis:names:tc:SAML:2.0:protocol\"/>"]))),
    assert_no_atom(P ++ ":Status"),
    assert_no_atom("xmlns:" ++ P).

namespace_uri_with_references_or_space_makes_no_atom_test() ->
    A = fresh(),
    lists:foreach(fun(Sep) ->
        Uri = ["http://www.w3.org/2000/09/xmldsig#", Sep, A],
        try_decode(b64(response(["<samlp:Extensions xmlns:ds=\"", Uri, "\"/>"])))
    end, ["&#x20;", "&#9;", "\t", "\n", "\r\n", " ", "&amp;"]),
    New = [S || S <- [" ", "\t", "\n", "&"],
                is_atom_name("http://www.w3.org/2000/09/xmldsig#" ++ S ++ A)],
    ?assertEqual([], New).

processing_instruction_makes_no_atom_test() ->
    Before = fresh(),
    Inside = fresh(),
    After = fresh(),
    try_decode(b64(["<?", Before, " x?>", response("")])),
    try_decode(b64(response(["<?", Inside, " x?>"]))),
    try_decode(b64([response(""), "<?", After, " x?>"])),
    lists:foreach(fun assert_no_atom/1, [Before, Inside, After]).

trailing_element_makes_no_atom_test() ->
    N = fresh(),
    M = fresh(),
    try_decode(b64([response(""), "<", N, "/>"])),
    try_decode(b64([response(""), "<!-- c --><", M, " a=\"b\"/>"])),
    assert_no_atom(N),
    assert_no_atom(M).

declared_encoding_makes_no_atom_test() ->
    N = fresh(),
    try_decode(b64(["<?xml version=\"1.0\" encoding=\"", N, "\"?>", response("")])),
    M = fresh(),
    try_decode(b64(["<?xml version=\"1.0\" x=\">\" encoding=\"", M, "\"?>", response("")])),
    assert_no_atom(N),
    assert_no_atom(M).

fresh_names_in_encrypted_assertion_make_no_atoms_test_() ->
    {timeout, 60, fun() ->
        Key = rsa_key(),
        N = fresh(),
        Plain = ["<saml:Assertion xmlns:saml=\"", ?SAML, "\" Version=\"2.0\"><", N, "/></saml:Assertion>"],
        try esaml_sp:validate_assertion(decode(b64(encrypted_response(Plain, Key))), unsigned_sp(Key))
        catch _:_ -> ok
        end,
        assert_no_atom(N)
    end}.

atom_table_headroom_is_enforced_test() ->
    %% Backstop: SAML parsing stops long before the atom table can fill.
    application:set_env(esaml, atom_ceiling, 1),
    try
        assert_refused(b64(response("")))
    after
        application:unset_env(esaml, atom_ceiling)
    end.

common_idp_documents_still_parse_test() ->
    Doc = ["<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n",
           "<saml2p:Response xmlns:saml2p=\"", ?SAMLP, "\" xmlns:xs=\"http://www.w3.org/2001/XMLSchema\" ",
           "ID=\"_1\" Version=\"2.0\" IssueInstant=\"2026-01-01T00:00:00Z\" Destination=\"x\" InResponseTo=\"y\">",
           "<saml2:Issuer xmlns:saml2=\"", ?SAML, "\" Format=\"urn:oasis:names:tc:SAML:2.0:nameid-format:entity\">i</saml2:Issuer>",
           "<ds:Signature xmlns:ds=\"http://www.w3.org/2000/09/xmldsig#\"><ds:SignedInfo>",
           "<ds:CanonicalizationMethod Algorithm=\"http://www.w3.org/2001/10/xml-exc-c14n#\"/>",
           "<ds:Reference URI=\"#_1\"><ds:Transforms><ds:Transform Algorithm=\"a\">",
           "<ec:InclusiveNamespaces xmlns:ec=\"http://www.w3.org/2001/10/xml-exc-c14n#\" PrefixList=\"xs\"/>",
           "</ds:Transform></ds:Transforms></ds:Reference></ds:SignedInfo></ds:Signature>",
           "<!-- comment -->",
           "<saml2:Assertion xmlns:saml2=\"", ?SAML, "\" xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\" ID=\"_2\">",
           "<saml2:AttributeStatement><saml2:Attribute Name=\"n\" NameFormat=\"f\" FriendlyName=\"g\">",
           "<saml2:AttributeValue xsi:type=\"xs:string\">Zo", 16#C3, 16#AB, " <![CDATA[<x>]]></saml2:AttributeValue>",
           "</saml2:Attribute></saml2:AttributeStatement></saml2:Assertion></saml2p:Response>\n"],
    ?assertMatch(#xmlElement{name = 'saml2p:Response'}, decode(b64(Doc))).

operator_can_allow_extra_names_test() ->
    N = fresh(),
    Doc = b64(response(["<samlp:Extensions><", N, "/></samlp:Extensions>"])),
    assert_refused(Doc),
    application:set_env(esaml, extra_xml_names, [N]),
    try
        ?assertMatch(#xmlElement{name = 'samlp:Response'}, decode(Doc))
    after
        application:unset_env(esaml, extra_xml_names)
    end.

signed_assertion_still_validates_test_() ->
    {timeout, 60, fun() ->
        {Key, Cert} = idp(),
        Doc = response(signed(assertion(#{name_id => "alice"}), Key, Cert)),
        ?assertMatch({ok, #esaml_assertion{subject = #esaml_subject{name = "alice"}}},
                     esaml_sp:validate_assertion(decode(b64(Doc)), signed_sp(Cert)))
    end}.

%% Compatibility: XML Encryption pads CBC plaintext after the root element.
cbc_encrypted_assertion_with_padding_still_validates_test_() ->
    {timeout, 60, fun() ->
        Key = rsa_key(),
        lists:foreach(fun(Extra) ->
            Base = assertion(#{}),
            %% Pad with white space so that every padding length is exercised.
            Plain = <<Base/binary, (binary:copy(<<" ">>, Extra))/binary>>,
            Doc = cbc_encrypted_response(Plain, Key),
            ?assertMatch({Extra, {ok, #esaml_assertion{}}},
                         {Extra, esaml_sp:validate_assertion(decode(b64(Doc)), unsigned_sp(Key))})
        end, lists:seq(0, 15))
    end}.

%% ---------------------------------------------------------------------------
%% CVE-2026-86696: atoms from status codes and attribute names
%% ---------------------------------------------------------------------------

unsigned_logout_response_status_makes_no_atom_test() ->
    N = fresh(),
    Doc = ["<samlp:LogoutResponse xmlns:samlp=\"", ?SAMLP, "\" Version=\"2.0\" ",
           "IssueInstant=\"2026-01-01T00:00:00Z\"><samlp:Status><samlp:StatusCode Value=\"urn:x:",
           N, "\"/></samlp:Status></samlp:LogoutResponse>"],
    ?assertMatch({error, _},
                 esaml_sp:validate_logout_response(decode(b64(Doc)), #esaml_sp{})),
    assert_no_atom(N).

standard_status_codes_keep_their_atoms_test() ->
    Decode = fun(Code) ->
        Doc = ["<samlp:LogoutResponse xmlns:samlp=\"", ?SAMLP, "\" Version=\"2.0\" ",
               "IssueInstant=\"2026-01-01T00:00:00Z\"><samlp:Status><samlp:StatusCode ",
               "Value=\"urn:oasis:names:tc:SAML:2.0:status:", Code,
               "\"/></samlp:Status></samlp:LogoutResponse>"],
        {ok, #esaml_logoutresp{status = S}} = esaml:decode_logout_response(decode(b64(Doc))),
        S
    end,
    ?assertEqual(success, Decode("Success")),
    ?assertEqual(denied, Decode("RequestDenied")),
    ?assertEqual('Requester', Decode("Requester")),
    ?assertEqual('PartialLogout', Decode("PartialLogout")).

attribute_names_make_no_atoms_test() ->
    A = fresh(),
    B = fresh(),
    Xml = decode(b64(assertion(#{attributes =>
        [["<saml:Attribute Name=\"", A, "\"><saml:AttributeValue>1</saml:AttributeValue></saml:Attribute>"],
         ["<saml:Attribute Name=\"http://schemas.example.test/claims/", B,
          "\"><saml:AttributeValue>2</saml:AttributeValue></saml:Attribute>"]]}))),
    {ok, #esaml_assertion{attributes = Attrs}} = esaml:decode_assertion(Xml),
    assert_no_atom(A),
    assert_no_atom(B),
    ?assertEqual([{A, "1"}, {B, "2"}], lists:sort(Attrs)).

%% ---------------------------------------------------------------------------
%% CVE-2026-53424 (library half): the duplicate check must see a digest that
%% covers the signed assertion only.
%% ---------------------------------------------------------------------------

duplicate_digest_ignores_unsigned_response_content_test_() ->
    {timeout, 60, fun() ->
        {Key, Cert} = idp(),
        A = signed(assertion(#{}), Key, Cert),
        Self = self(),
        Fun = fun(_, Digest) -> Self ! {digest, Digest}, ok end,
        Digest = fun(Doc) ->
            {ok, _} = esaml_sp:validate_assertion(decode(b64(Doc)), Fun, signed_sp(Cert)),
            receive {digest, D} -> D after 1000 -> error(no_digest) end
        end,
        First = Digest(response(A)),
        ?assertEqual(First, Digest(response(A, "_another_response_id"))),
        ?assertEqual(First, Digest(response(["<!-- x -->", A]))),
        ?assertEqual(First, Digest(response(["<samlp:Extensions/>", A]))),
        Commented = binary:replace(iolist_to_binary(A), <<"</saml:Issuer>">>, <<"<!--c--></saml:Issuer>">>),
        ?assertEqual(First, Digest(response(Commented))),
        Other = signed(assertion(#{id => "_other"}), Key, Cert),
        ?assertNotEqual(First, Digest(response(Other)))
    end}.

%% ---------------------------------------------------------------------------
%% helpers
%% ---------------------------------------------------------------------------

fresh() ->
    "zz" ++ integer_to_list(erlang:unique_integer([positive]))
        ++ "q" ++ integer_to_list(erlang:system_time()).

is_atom_name(Name) ->
    try list_to_existing_atom(Name) of
        _ -> true
    catch
        error:badarg -> false
    end.

assert_no_atom(Name) ->
    ?assertEqual({Name, false}, {Name, is_atom_name(Name)}).

b64(Doc) -> base64:encode(iolist_to_binary(Doc)).

deflated(Doc) -> base64:encode(zlib:zip(iolist_to_binary(Doc))).

decode(Payload) -> esaml_binding:decode_response(<<>>, Payload).

try_decode(Payload) ->
    try decode(Payload) of
        _ -> ok
    catch
        _:_ -> ok
    end.

%% Refused means the hardened decoder raised its own refusal. A parser crash on
%% the way to reading the payload does not count.
assert_refused(Payload) -> assert_refused(<<>>, Payload).

assert_refused(Encoding, Payload) ->
    Result = try esaml_binding:decode_response(Encoding, Payload) of
        _ -> accepted
    catch
        error:{saml_payload_refused, _} -> refused;
        Class:Reason -> {crashed, Class, element_or_self(Reason)}
    end,
    ?assertEqual(refused, Result).

element_or_self(R) when is_tuple(R), tuple_size(R) > 0 -> element(1, R);
element_or_self(R) -> R.

with_dtd(Fun) ->
    Path = filename:join(os:getenv("TMPDIR", "/tmp"), "esaml-test-" ++ fresh() ++ ".dtd"),
    ok = file:write_file(Path, <<"<!ELEMENT unused EMPTY>">>),
    try Fun(Path) after file:delete(Path) end.

response(Inner) -> response(Inner, "_response").

response(Inner, Id) ->
    iolist_to_binary(
      ["<samlp:Response xmlns:samlp=\"", ?SAMLP, "\" xmlns:saml=\"", ?SAML, "\" ID=\"", Id,
       "\" Version=\"2.0\" IssueInstant=\"2026-01-01T00:00:00Z\"><samlp:Status><samlp:StatusCode ",
       "Value=\"urn:oasis:names:tc:SAML:2.0:status:Success\"/></samlp:Status>", Inner,
       "</samlp:Response>"]).

saml_time(Offset) ->
    Now = calendar:datetime_to_gregorian_seconds(calendar:universal_time()),
    esaml_util:datetime_to_saml(calendar:gregorian_seconds_to_datetime(Now + Offset)).

assertion(Opts) ->
    Later = saml_time(300),
    iolist_to_binary(
      ["<saml:Assertion xmlns:saml=\"", ?SAML, "\" ID=\"", maps:get(id, Opts, "_assertion"),
       "\" Version=\"2.0\" IssueInstant=\"", saml_time(0), "\">",
       "<saml:Issuer>https://idp.example.test</saml:Issuer><saml:Subject><saml:NameID>",
       maps:get(name_id, Opts, "alice"), "</saml:NameID>",
       "<saml:SubjectConfirmation Method=\"urn:oasis:names:tc:SAML:2.0:cm:bearer\">",
       "<saml:SubjectConfirmationData Recipient=\"", ?CONSUME, "\" NotOnOrAfter=\"", Later,
       "\"/></saml:SubjectConfirmation></saml:Subject><saml:Conditions NotOnOrAfter=\"", Later,
       "\"><saml:AudienceRestriction><saml:Audience>", ?ENTITY,
       "</saml:Audience></saml:AudienceRestriction></saml:Conditions>",
       "<saml:AttributeStatement>", maps:get(attributes, Opts, []), "</saml:AttributeStatement>",
       "</saml:Assertion>"]).

rsa_key() -> public_key:generate_key({rsa, 2048, 65537}).

idp() ->
    Key = rsa_key(),
    #{cert := Cert} = public_key:pkix_test_root_cert("idp", [{key, Key}]),
    {Key, Cert}.

signed(Assertion, Key, Cert) ->
    {El, _} = xmerl_scan:string(binary_to_list(Assertion), [{namespace_conformant, true}]),
    Xml = unicode:characters_to_binary(
            lists:flatten(xmerl:export([xmerl_dsig:sign(El, Key, Cert)], xmerl_xml))),
    [_Declaration, Body] = binary:split(Xml, <<"?>">>),
    Body.

signed_sp(Cert) ->
    #esaml_sp{idp_signs_assertions = true, idp_signs_envelopes = false,
              trusted_fingerprints = [{sha256, crypto:hash(sha256, Cert)}],
              consume_uri = ?CONSUME, entity_id = ?ENTITY, metadata_uri = ?ENTITY}.

unsigned_sp(Key) ->
    #esaml_sp{key = Key, idp_signs_assertions = false, idp_signs_envelopes = false,
              consume_uri = ?CONSUME, entity_id = ?ENTITY, metadata_uri = ?ENTITY}.

cbc_encrypted_response(Plain, Key) ->
    K = crypto:strong_rand_bytes(16),
    IV = crypto:strong_rand_bytes(16),
    N = 16 - (byte_size(Plain) rem 16),
    Padded = <<Plain/binary, (binary:copy(<<N>>, N))/binary>>,
    CT = crypto:crypto_one_time(aes_128_cbc, K, IV, Padded, true),
    encrypted_response("http://www.w3.org/2001/04/xmlenc#aes128-cbc", K, <<IV/binary, CT/binary>>, Key).

encrypted_response(Plain, Key) ->
    K = crypto:strong_rand_bytes(16),
    IV = crypto:strong_rand_bytes(12),
    {CT, Tag} = crypto:crypto_one_time_aead(aes_128_gcm, K, IV, iolist_to_binary(Plain), <<>>, true),
    encrypted_response("http://www.w3.org/2009/xmlenc11#aes128-gcm", K,
                       <<IV/binary, CT/binary, Tag/binary>>, Key).

encrypted_response(Algorithm, K, Cipher, Key) ->
    Pub = #'RSAPublicKey'{modulus = Key#'RSAPrivateKey'.modulus,
                          publicExponent = Key#'RSAPrivateKey'.publicExponent},
    EK = public_key:encrypt_public(K, Pub, [{rsa_padding, rsa_pkcs1_oaep_padding}]),
    response(
      ["<saml:EncryptedAssertion><xenc:EncryptedData xmlns:xenc=\"http://www.w3.org/2001/04/xmlenc#\">",
       "<xenc:EncryptionMethod Algorithm=\"", Algorithm, "\"/>",
       "<ds:KeyInfo xmlns:ds=\"http://www.w3.org/2000/09/xmldsig#\"><xenc:EncryptedKey>",
       "<xenc:EncryptionMethod Algorithm=\"http://www.w3.org/2001/04/xmlenc#rsa-oaep-mgf1p\"/>",
       "<xenc:CipherData><xenc:CipherValue>", base64:encode(EK),
       "</xenc:CipherValue></xenc:CipherData></xenc:EncryptedKey></ds:KeyInfo>",
       "<xenc:CipherData><xenc:CipherValue>", base64:encode(Cipher),
       "</xenc:CipherValue></xenc:CipherData></xenc:EncryptedData></saml:EncryptedAssertion>"]).
