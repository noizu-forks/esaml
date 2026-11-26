%% esaml - SAML for erlang
%%
%% Copyright (c) 2013, Alex Wilson and the University of Queensland
%% All rights reserved.
%%
%% Distributed subject to the terms of the 2-clause BSD license, see
%% the LICENSE file in the root of the distribution.

%% @doc Utility functions
-module(esaml_util).

-include_lib("xmerl/include/xmerl.hrl").
-include_lib("public_key/include/public_key.hrl").
-include("esaml.hrl").

-export([datetime_to_saml/1, saml_to_datetime/1]).
-export([start_ets/0, check_dupe_ets/2]).
-export([folduntil/3, thread/2, threaduntil/2]).
-export([build_nsinfo/2]).
-export([load_private_key/1, import_private_key/2]).
-export([load_certificate_chain/1, import_certificate_chain/2]).
-export([load_certificate/1, import_certificate/2]).
-export([load_metadata/2, load_metadata/1]).
-export([convert_fingerprints/1]).
-export([unique_id/0]).
-export([scan_untrusted_xml/1, bounded_inflate/1, refuse_payload/1, xml_scan_options/0]).

%% Real SAML messages are a few KB to about 100 KB.
-define(MAX_XML_BYTES, 524288).

%% @doc Converts various ascii hex/base64 fingerprint formats to binary
-spec convert_fingerprints([string() | binary()]) -> [binary()].
convert_fingerprints(FPs) ->
    FPSources = FPs ++ esaml:config(trusted_fingerprints, []),
    lists:map(fun(Print) ->
        if is_list(Print) ->
            case string:tokens(Print, ":") of
                [Type, Base64] ->
                    Hash = base64:decode(Base64),
                    case string:to_lower(Type) of
                        "sha" -> {sha, Hash};
                        "sha1" -> {sha, Hash};
                        "md5" -> {md5, Hash};
                        "sha256" -> {sha256, Hash};
                        "sha384" -> {sha384, Hash};
                        "sha512" -> {sha512, Hash}
                    end;
                [_] -> error("unknown fingerprint format");
                HexParts ->
                    list_to_binary([list_to_integer(P, 16) || P <- HexParts])
            end;
        is_binary(Print) ->
            Print;
        true ->
            error("unknown fingerprint format")
        end
    end, FPSources).

%% @doc Converts a calendar:datetime() into SAML time string
-spec datetime_to_saml(calendar:datetime()) -> esaml:datetime().
datetime_to_saml(Time) ->
    {{Y,Mo,D}, {H, Mi, S}} = Time,
    lists:flatten(io_lib:format("~4.10.0B-~2.10.0B-~2.10.0BT~2.10.0B:~2.10.0B:~2.10.0BZ", [Y, Mo, D, H, Mi, S])).

%% @doc Converts a SAML time string into a calendar:datetime()
%%
%% Inverse of datetime_to_saml/1
-spec saml_to_datetime(esaml:datetime()) -> calendar:datetime().
saml_to_datetime(Stamp) ->
    StampBin = if is_list(Stamp) -> list_to_binary(Stamp); true -> Stamp end,
    <<YBin:4/binary, "-", MoBin:2/binary, "-", DBin:2/binary, "T",
        HBin:2/binary, ":", MiBin:2/binary, ":", SBin:2/binary, Rest/binary>> = StampBin,
    %% check that time in UTC timezone because we don't handle another timezones properly
    $Z = binary:last(Rest),
    F = fun(B) -> list_to_integer(binary_to_list(B)) end,
    {{F(YBin), F(MoBin), F(DBin)}, {F(HBin), F(MiBin), F(SBin)}}.

%% @private
-spec folduntil(F :: fun(), Acc :: term(), List :: []) -> AccOut :: term().
folduntil(_F, Acc, []) -> Acc;
folduntil(F, Acc, [Next | Rest]) ->
    case F(Next, Acc) of
        {stop, AccOut} -> AccOut;
        NextAcc -> folduntil(F, NextAcc, Rest)
    end.

%% @private
thread([], Acc) -> Acc;
thread([F | Rest], Acc) ->
    thread(Rest, F(Acc)).

%% @private
-spec threaduntil([fun((Acc :: term()) -> {error, term()} | {stop, term()} | term())], InitAcc::term()) -> {ok, term()} | {error, term()}.
threaduntil([], Acc) -> {ok, Acc};
threaduntil([F | Rest], Acc) ->
    case (catch F(Acc)) of
        {'EXIT', Reason} ->
            {error, Reason};
        {error, Reason} ->
            {error, Reason};
        {stop, LastAcc} ->
            {ok, LastAcc};
        NextAcc ->
            threaduntil(Rest, NextAcc)
    end.

%% @private
-spec build_nsinfo(#xmlNamespace{}, #xmlElement{}) -> #xmlElement{}.
build_nsinfo(Ns, Attr = #xmlAttribute{name = Name}) ->
    case string:tokens(atom_to_list(Name), ":") of
        [NsPrefix, Rest] -> Attr#xmlAttribute{namespace = Ns, nsinfo = {NsPrefix, Rest}};
        _ -> Attr#xmlAttribute{namespace = Ns}
    end;
build_nsinfo(Ns, Elem = #xmlElement{name = Name, content = Kids, attributes = Attrs}) ->
    Elem2 = case string:tokens(atom_to_list(Name), ":") of
        [NsPrefix, Rest] -> Elem#xmlElement{namespace = Ns, nsinfo = {NsPrefix, Rest}};
        _ -> Elem#xmlElement{namespace = Ns}
    end,
    Elem2#xmlElement{attributes = [build_nsinfo(Ns, Attr) || Attr <- Attrs],
                    content = [build_nsinfo(Ns, Kid) || Kid <- Kids]};
build_nsinfo(_Ns, Other) -> Other.

%% @private
start_ets() ->
    case erlang:whereis(esaml_ets_table_owner) of
        undefined ->
            create_tables();
        Pid ->
            Pid ! {self(), check_ready},
            receive
                {Pid, ready} -> {ok, Pid}
            end
    end.

%% @private
create_tables() ->
    Caller = self(),
    Pid = spawn_link(fun() ->
              register(esaml_ets_table_owner, self()),
              ets:new(esaml_assertion_seen, [set, public, named_table]),
              ets:new(esaml_privkey_cache, [set, public, named_table]),
              ets:new(esaml_certbin_cache, [set, public, named_table]),
              ets:new(esaml_idp_meta_cache, [set, public, named_table]),
              Caller ! {self(), ready},
              ets_table_owner()
         end),

    receive
        {Pid, ready} -> ok
    end,

    {ok, Pid}.

%% @private
ets_table_owner() ->
    receive
        stop ->
            ok;
        {Caller, check_ready} ->
            Caller ! {self(), ready},
            ets_table_owner();
        _ ->
            ets_table_owner()
    end.

%% @doc Loads a private key from a file on disk (or ETS memory cache)
-spec load_private_key(Path :: string()) -> #'RSAPrivateKey'{}.
load_private_key(Path) ->
    case ets:lookup(esaml_privkey_cache, Path) of
        [{_, Key}] ->
            Key;
        _ ->
            {ok, KeyFile} = file:read_file(Path),
            do_import_private_key(KeyFile, Path)
    end.

-spec import_private_key(EncodedKey :: string(), Identifier :: term()) -> #'RSAPrivateKey'{}.
import_private_key(EncodedKey, Identifier) ->
    case ets:lookup(esaml_privkey_cache, Identifier) of
        [{_, Key}] -> Key;
        _ -> do_import_private_key(EncodedKey, Identifier)
    end.

do_import_private_key(EncodedKey, Identifier) ->
    [KeyEntry] = public_key:pem_decode(EncodedKey),
    Key = case public_key:pem_entry_decode(KeyEntry) of
              #'PrivateKeyInfo'{privateKey = KeyData} ->
                  KeyDataBin = if is_list(KeyData) -> list_to_binary(KeyData);
                                  true -> KeyData
                               end,
                  public_key:der_decode('RSAPrivateKey', KeyDataBin);
              Other -> Other
          end,
    ets:insert(esaml_privkey_cache, {Identifier, Key}),
    Key.

-spec load_certificate(Path :: string()) -> binary().
load_certificate(Path) ->
    [CertBin] = load_certificate_chain(Path),
    CertBin.

-spec import_certificate(EncodedCert :: string(), Identifier :: term()) -> binary().
import_certificate(EncodedCert, Identifier) ->
    [CertBin] = import_certificate_chain(EncodedCert, Identifier),
    CertBin.

%% @doc Loads certificate chain from a file on disk (or ETS memory cache)
-spec load_certificate_chain(Path :: string()) -> [binary()].
load_certificate_chain(Path) ->
    case ets:lookup(esaml_certbin_cache, Path) of
        [{_, CertChain}] ->
            CertChain;
        _ ->
            {ok, EncodedCert} = file:read_file(Path),
            do_import_certificate_chain(EncodedCert, Path)
    end.

%% @doc Loads certificate chain from a file on disk (or ETS memory cache)
-spec import_certificate_chain(EncodedCerts :: string(), Identifier :: string()) -> [binary()].
import_certificate_chain(EncodedCerts, Identifier) ->
    case ets:lookup(esaml_certbin_cache, Identifier) of
        [{_, CertChain}] ->
            CertChain;
        _ ->
            do_import_certificate_chain(EncodedCerts, Identifier)
    end.

do_import_certificate_chain(EncodedCerts, Identifier) ->
    CertChain = [CertBin || {'Certificate', CertBin, not_encrypted} <- public_key:pem_decode(EncodedCerts)],
    ets:insert(esaml_certbin_cache, {Identifier, CertChain}),
    CertChain.

%% @doc Reads IDP metadata from a URL (or ETS memory cache) and validates the signature
-spec load_metadata(Url :: string(), Fingerprints :: [string() | binary()]) -> esaml:idp_metadata().
load_metadata(Url, FPs) ->
    Fingerprints = convert_fingerprints(FPs),
    case ets:lookup(esaml_idp_meta_cache, Url) of
        [{Url, Meta}] -> Meta;
        _ ->
            {ok, {{_Ver, 200, _}, _Headers, Body}} = httpc:request(get, {Url, []}, [{autoredirect, true}, {timeout, 3000}], []),
            {Xml, _} = xmerl_scan:string(Body, xml_scan_options()),
            case xmerl_dsig:verify(Xml, Fingerprints) of
                ok -> ok;
                Err -> error(Err)
            end,
            {ok, Meta = #esaml_idp_metadata{}} = esaml:decode_idp_metadata(Xml),
            ets:insert(esaml_idp_meta_cache, {Url, Meta}),
            Meta
    end.

%% @doc Reads IDP metadata from a URL (or ETS memory cache)
-spec load_metadata(Url :: string()) -> esaml:idp_metadata().
load_metadata(Url) ->
    case ets:lookup(esaml_idp_meta_cache, Url) of
        [{Url, Meta}] -> Meta;
        _ ->
            Timeout = application:get_env(esaml, load_metadata_timeout, 15000),
            {ok, {{_Ver, 200, _}, _Headers, Body}} = httpc:request(get, {Url, []}, [{autoredirect, true}, {timeout, Timeout}], []),
            {Xml, _} = xmerl_scan:string(Body, xml_scan_options()),
            {ok, Meta = #esaml_idp_metadata{}} = esaml:decode_idp_metadata(Xml),
            ets:insert(esaml_idp_meta_cache, {Url, Meta}),
            Meta
    end.

%% @doc Checks for a duplicate assertion using ETS tables in memory on all available nodes.
%%
%% This is a helper to be used as a DuplicateFun with esaml_sp:validate_assertion/3.
%% If you aren't using standard erlang distribution for your app, you probably don't
%% want to use this.
-spec check_dupe_ets(esaml:assertion(), Digest :: binary()) -> ok | {error, duplicate_assertion}.
check_dupe_ets(A, Digest) ->
    Now = erlang:localtime_to_universaltime(erlang:localtime()),
    NowSecs = calendar:datetime_to_gregorian_seconds(Now),
    DeathSecs = esaml:stale_time(A),
    {ResL, _BadNodes} = rpc:multicall(erlang, apply, [fun() ->
        case (catch ets:lookup(esaml_assertion_seen, Digest)) of
            [{Digest, seen} | _] -> seen;
            _ -> ok
        end
    end, []]),
    case lists:member(seen, ResL) of
        true ->
            {error, duplicate_assertion};
        _ ->
            Until = DeathSecs - NowSecs + 1,
            rpc:multicall(erlang, apply, [fun() ->
                case ets:info(esaml_assertion_seen) of
                    undefined ->
                        Me = self(),
                        Pid = spawn(fun() ->
                            register(esaml_ets_table_owner, self()),
                            ets:new(esaml_assertion_seen, [set, public, named_table]),
                            ets:new(esaml_privkey_cache, [set, public, named_table]),
                            ets:new(esaml_certbin_cache, [set, public, named_table]),
                            ets:insert(esaml_assertion_seen, {Digest, seen}),
                            Me ! {self(), ping},
                            ets_table_owner()
                        end),
                        receive
                            {Pid, ping} -> ok
                        end;
                    _ ->
                        ets:insert(esaml_assertion_seen, {Digest, seen})
                end,
                {ok, _} = timer:apply_after(Until * 1000, erlang, apply, [fun() ->
                    ets:delete(esaml_assertion_seen, Digest)
                end, []])
            end, []]),
            ok
    end.

% TODO: switch to uuid_erl hex pkg
unique_id() ->
    "id"
      ++ integer_to_list(erlang:system_time())
      ++ integer_to_list(erlang:unique_integer([positive])).

%% @doc Parser options for every XML document that did not come from this node:
%% no entity declarations and no reads of external files or URLs.
-spec xml_scan_options() -> list().
xml_scan_options() ->
    [{namespace_conformant, true},
     {allow_entities, false},
     {fetch_fun, fun refuse_fetch/2}].

refuse_fetch(_Spec, _State) ->
    refuse_payload(external_fetch_not_allowed).

%% @doc Raise the error used for every refused SAML payload.
-spec refuse_payload(Reason :: atom()) -> no_return().
refuse_payload(Reason) ->
    erlang:error({saml_payload_refused, Reason}).

%% @doc Parse an XML payload that an unauthenticated party can control.
%%
%% Raises `error:{saml_payload_refused, Reason}' and never reaches xmerl_scan
%% when the payload
%% <ul>
%% <li>is over 512 KB,</li>
%% <li>is not plain UTF-8 XML 1.0 (a NUL byte, another declared encoding),</li>
%% <li>holds a DOCTYPE or a processing instruction,</li>
%% <li>has anything but comments and white space after the root element,</li>
%% <li>uses an element name, attribute name, prefix or namespace URI that is
%% not already an atom. xmerl_scan makes an atom from each of those, and atoms
%% are never freed. Add names that an identity provider really uses to the
%% `extra_xml_names' application variable.</li>
%% </ul>
%% As a second line of defence it also refuses to parse at all once the node's
%% atom table is half full (`atom_ceiling' application variable).
-spec scan_untrusted_xml(binary()) -> #xmlElement{}.
scan_untrusted_xml(Xml) when is_binary(Xml) ->
    ok = check_atom_headroom(),
    ok = check_size(Xml),
    ok = check_markup(Xml),
    ok = check_namespace_literals(Xml),
    ok = check_names(Xml),
    try xmerl_scan:string(binary_to_list(Xml), xml_scan_options()) of
        {#xmlElement{} = Doc, _Rest} -> Doc;
        _ -> refuse_payload(bad_xml)
    catch
        exit:_ -> refuse_payload(bad_xml)
    end.

check_atom_headroom() ->
    Ceiling = application:get_env(esaml, atom_ceiling,
                                  erlang:system_info(atom_limit) div 2),
    case erlang:system_info(atom_count) < Ceiling of
        true -> ok;
        false ->
            error_logger:error_msg("esaml: atom table over ~p entries, refusing to parse SAML~n",
                                   [Ceiling]),
            refuse_payload(atom_table_headroom)
    end.

check_size(Xml) when byte_size(Xml) > ?MAX_XML_BYTES ->
    refuse_payload(payload_too_large);
check_size(_) ->
    ok.

check_markup(Xml) ->
    %% A NUL byte means UTF-16 or UCS-4, which would hide markup from the checks.
    binary:match(Xml, <<0>>) =:= nomatch orelse refuse_payload(encoding_not_allowed),
    re:run(Xml, "<!DOCTYPE|<!ENTITY", [caseless, {capture, none}]) =:= nomatch
        orelse refuse_payload(doctype_not_allowed),
    %% The only "<?" allowed is a plain XML 1.0 UTF-8 declaration at the start.
    Body = strip_declaration(Xml),
    binary:match(Body, <<"<?">>) =:= nomatch
        orelse refuse_payload(declaration_or_instruction_not_allowed),
    ok.

strip_declaration(Xml) ->
    Declaration =
        "\\A(?:\\xEF\\xBB\\xBF)?<\\?xml"
        "\\s+version\\s*=\\s*(?:\"1\\.0\"|'1\\.0')"
        "(?:\\s+encoding\\s*=\\s*(?:\"(?i:utf-8)\"|'(?i:utf-8)'))?"
        "(?:\\s+standalone\\s*=\\s*(?:\"(?:yes|no)\"|'(?:yes|no)'))?"
        "\\s*\\?>",
    case re:run(Xml, Declaration, [{capture, first, index}]) of
        {match, [{0, Length}]} ->
            binary:part(Xml, Length, byte_size(Xml) - Length);
        nomatch ->
            Xml
    end.

%% A namespace URI becomes an atom. Require it to be written as plain printable
%% ASCII, so that the name check below and xmerl_scan cannot read it differently
%% (references and white space are normalised by parsers).
check_namespace_literals(Xml) ->
    Re = "xmlns(?::[^\\s=<>\"']+)?\\s*=\\s*(?:\"([^\"]*)\"|'([^']*)')",
    case re:run(Xml, Re, [global, {capture, all_but_first, binary}]) of
        nomatch -> ok;
        {match, Matches} ->
            lists:all(fun(Groups) -> plain_ascii(iolist_to_binary(Groups)) end, Matches)
                orelse refuse_payload(namespace_not_allowed),
            ok
    end.

plain_ascii(Bin) ->
    lists:all(fun(C) -> C > 16#20 andalso C < 16#7F andalso C =/= $& end,
              binary_to_list(Bin)).

%% Read the document with the SAX parser, which reports names as strings, and
%% require every name that xmerl_scan would turn into an atom to be one already.
check_names(Xml) ->
    ok = ensure_vocabulary(),
    Options = [{event_fun, fun name_event/3}, {event_state, ok}],
    Result = try xmerl_sax_parser:stream(Xml, Options)
             catch _:_ -> failed
             end,
    case Result of
        {ok, ok, Rest} -> check_trailing(Rest);
        {saml_name, _Location, Name, _EndTags, _State} ->
            error_logger:warning_msg("esaml: refused unknown XML name ~tp~n",
                                     [lists:sublist(Name, 120)]),
            refuse_payload(unknown_xml_name);
        _ -> refuse_payload(bad_xml)
    end.

check_trailing(Rest) when is_binary(Rest) ->
    Left = re:replace(Rest, "<!--.*?-->", "", [global, dotall, {return, binary}]),
    %% Text without markup cannot create a name. XML encryption padding can
    %% leave such bytes behind a decrypted assertion.
    binary:match(Left, <<"<">>) =:= nomatch orelse refuse_payload(content_after_root),
    ok.

name_event({startPrefixMapping, Prefix, Uri}, _Location, State) ->
    require_atoms([qname("xmlns", Prefix), Uri]),
    State;
name_event({startElement, Uri, Local, {Prefix, Local}, Attributes}, _Location, State) ->
    require_atoms([Uri, Local, qname(Prefix, Local)]),
    lists:foreach(fun({AttrUri, AttrPrefix, AttrLocal, _Value}) ->
        require_atoms([AttrUri, AttrLocal, qname(AttrPrefix, AttrLocal)])
    end, Attributes),
    State;
name_event(_Event, _Location, State) ->
    State.

qname("", Local) -> Local;
qname(Prefix, "") -> Prefix;
qname(Prefix, Local) -> Prefix ++ ":" ++ Local.

require_atoms(Names) ->
    lists:foreach(fun(Name) ->
        Ascii = lists:all(fun(C) -> C < 16#80 end, Name),
        try
            true = Ascii,
            list_to_existing_atom(Name)
        catch
            error:_ -> throw({saml_name, Name})
        end
    end, Names).

ensure_vocabulary() ->
    case persistent_term:get({?MODULE, vocabulary}, false) of
        true -> ok;
        false ->
            lists:foreach(fun list_to_atom/1, vocabulary()),
            persistent_term:put({?MODULE, vocabulary}, true)
    end,
    %% Operator-configured names, for identity providers that use their own.
    lists:foreach(fun list_to_atom/1, application:get_env(esaml, extra_xml_names, [])).

%% The names that SAML 2.0, XML-DSig and XML-Enc messages use. Every prefix is
%% combined with every local name, because identity providers choose their own
%% prefixes.
vocabulary() ->
    Prefixes = ["saml", "saml2", "samlp", "saml2p", "ds", "dsig", "dsig11", "xenc", "xenc11",
                "enc", "xs", "xsd", "xsi", "ec", "md", "x500", "xml", "xmlns"]
               ++ ["ns" ++ integer_to_list(N) || N <- lists:seq(0, 9)],
    Namespaces = ["urn:oasis:names:tc:SAML:2.0:protocol",
                  "urn:oasis:names:tc:SAML:2.0:assertion",
                  "urn:oasis:names:tc:SAML:2.0:metadata",
                  "urn:oasis:names:tc:SAML:2.0:profiles:attribute:X500",
                  "http://www.w3.org/2000/09/xmldsig#",
                  "http://www.w3.org/2001/04/xmldsig-more#",
                  "http://www.w3.org/2009/xmldsig11#",
                  "http://www.w3.org/2001/04/xmlenc#",
                  "http://www.w3.org/2009/xmlenc11#",
                  "http://www.w3.org/2001/10/xml-exc-c14n#",
                  "http://www.w3.org/2001/XMLSchema",
                  "http://www.w3.org/2001/XMLSchema-instance",
                  "http://www.w3.org/XML/1998/namespace",
                  "http://www.w3.org/2000/xmlns/"],
    Locals = string:lexemes(
        "AuthnRequest Response LogoutRequest LogoutResponse Status StatusCode StatusMessage "
        "StatusDetail Extensions NameIDPolicy RequestedAuthnContext Scoping IDPList IDPEntry "
        "GetComplete RequesterID SessionIndex Artifact ArtifactResolve ArtifactResponse "
        "Assertion EncryptedAssertion Issuer Subject NameID BaseID EncryptedID "
        "SubjectConfirmation SubjectConfirmationData Conditions Condition AudienceRestriction "
        "Audience OneTimeUse ProxyRestriction Advice AssertionIDRef AssertionURIRef Statement "
        "AuthnStatement SubjectLocality AuthnContext AuthnContextClassRef AuthnContextDeclRef "
        "AuthnContextDecl AuthenticatingAuthority AttributeStatement Attribute AttributeValue "
        "EncryptedAttribute AuthzDecisionStatement Action Evidence "
        "Signature SignedInfo CanonicalizationMethod SignatureMethod Reference Transforms "
        "Transform DigestMethod DigestValue SignatureValue KeyInfo KeyName KeyValue RSAKeyValue "
        "Modulus Exponent DSAKeyValue ECKeyValue X509Data X509Certificate X509IssuerSerial "
        "X509IssuerName X509SerialNumber X509SubjectName X509SKI X509CRL X509Digest "
        "RetrievalMethod Object Manifest SignatureProperties SignatureProperty "
        "HMACOutputLength XPath PGPData SPKIData MgmtData InclusiveNamespaces "
        "EncryptedData EncryptedKey EncryptionMethod CipherData CipherValue CipherReference "
        "KeySize OAEPparams MGF ReferenceList DataReference KeyReference CarriedKeyName "
        "AgreementMethod EncryptionProperties EncryptionProperty "
        "ID Id Version IssueInstant Destination Consent InResponseTo Format NameQualifier "
        "SPNameQualifier SPProvidedID Method NotBefore NotOnOrAfter Recipient Address "
        "AuthnInstant SessionNotOnOrAfter Name NameFormat FriendlyName Value Algorithm URI "
        "Type MimeType Encoding PrefixList AllowCreate ForceAuthn IsPassive ProtocolBinding "
        "AssertionConsumerServiceURL AssertionConsumerServiceIndex "
        "AttributeConsumingServiceIndex ProviderName Reason Comparison ProxyCount Loc DNSName "
        "Resource Decision Namespace Count ProviderID type nil lang space base schemaLocation",
        " "),
    ["", "xmlns" | Namespaces] ++ Locals ++ Prefixes
        ++ [P ++ ":" ++ N || P <- Prefixes, N <- Locals ++ Prefixes].

%% @doc Inflate raw DEFLATE data without ever holding more than 512 KB of output.
%%
%% Raises `error:data_error' on data that is not a complete raw DEFLATE stream,
%% as zlib:unzip/1 does, and refuses the payload when the input or the output is
%% over the limit.
-spec bounded_inflate(binary()) -> binary().
bounded_inflate(Data) when byte_size(Data) > ?MAX_XML_BYTES ->
    refuse_payload(payload_too_large);
bounded_inflate(Data) ->
    Z = zlib:open(),
    try
        ok = zlib:inflateInit(Z, -15),
        inflate_loop(Z, zlib:safeInflate(Z, Data), [], 0)
    after
        zlib:close(Z)
    end.

inflate_loop(Z, {Status, Output}, Acc, Size0) when Status =:= continue; Status =:= finished ->
    Size = Size0 + iolist_size(Output),
    Size =< ?MAX_XML_BYTES orelse refuse_payload(payload_too_large),
    case Status of
        continue ->
            inflate_loop(Z, zlib:safeInflate(Z, []), [Acc, Output], Size);
        finished ->
            %% Raises data_error when the stream was cut short.
            ok = zlib:inflateEnd(Z),
            iolist_to_binary([Acc, Output])
    end;
inflate_loop(_Z, {need_dictionary, _, _}, _Acc, _Size) ->
    erlang:error(data_error).

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

fingerprints_test() ->
    [<<0:128>>] = convert_fingerprints([<<0:128>>]),
    {'EXIT', _} = (catch convert_fingerprints(["testing"])),
    [<<0:32,1,10,3>>] = convert_fingerprints(["00:00:00:00:01:0a:03"]),
    Hash = crypto:hash(sha, <<"testing1234">>),
    [{sha,Hash}] = convert_fingerprints(["SHA:" ++ base64:encode_to_string(Hash)]),
    Sha256 = crypto:hash(sha256, <<"testing1234">>),
    [{sha256,Sha256},{md5,Hash}] = convert_fingerprints(["SHA256:" ++ base64:encode_to_string(Sha256), "md5:" ++ base64:encode_to_string(Hash)]),
    {'EXIT', _} = (catch convert_fingerprints(["SOMEALGO:AAAAA="])).

datetime_test() ->
    "2013-05-02T17:26:53Z" = datetime_to_saml({{2013,5,2},{17,26,53}}),
    {{1990,11,23},{18,1,1}} = saml_to_datetime("1990-11-23T18:01:01Z").

build_nsinfo_test() ->
    EmptyNs = #xmlNamespace{},
    FooNs = #xmlNamespace{nodes = [{"foo", 'urn:foo:'}]},

    E1 = #xmlElement{name = 'foo', content = [#xmlText{value = 'bar'}]},
    E1 = build_nsinfo(EmptyNs, E1),

    E2 = #xmlElement{name = 'foo:Blah', content = [#xmlText{value = 'bar'}]},
    E2Ns = E2#xmlElement{nsinfo = {"foo", "Blah"}, namespace = FooNs},
    E2Ns = build_nsinfo(FooNs, E2),

    E3 = #xmlElement{name = 'blah:George', content = [E2]},
    E3Ns = E3#xmlElement{nsinfo = {"blah", "George"}, namespace = FooNs, content = [E2Ns]},
    E3Ns = build_nsinfo(FooNs, E3).

key_load_test() ->
    start_ets(),
    KeyPath = "../test/selfsigned_key.pem",
    Key = load_private_key(KeyPath),
    ?assertEqual([{KeyPath, Key}], ets:lookup(esaml_privkey_cache, KeyPath)).

key_import_test() ->
    start_ets(),
    {ok, EncodedKey} = file:read_file("../test/selfsigned_key.pem"),
    Key = import_private_key(EncodedKey, my_key),
    ?assertEqual([{my_key, Key}], ets:lookup(esaml_privkey_cache, my_key)).

bad_key_load_test() ->
    start_ets(),
    KeyPath = "../test/bad_data.pem",
    ?assertException(error, {badmatch, []}, load_private_key(KeyPath)),
    ?assertEqual([], ets:lookup(esaml_privkey_cache, KeyPath)).

cert_load_test() ->
    start_ets(),
    CertPath = "../test/selfsigned.pem",
    Cert = load_certificate(CertPath),
    ?assertEqual([{CertPath, [Cert]}], ets:lookup(esaml_certbin_cache, CertPath)).

cert_import_test() ->
    start_ets(),
    {ok, EncodedCert} = file:read_file("../test/selfsigned.pem"),
    Cert = import_certificate(EncodedCert, my_cert),
    ?assertEqual([{my_cert, [Cert]}], ets:lookup(esaml_certbin_cache, my_cert)).

bad_cert_load_test() ->
    start_ets(),
    CertPath = "../test/bad_data.pem",
    ?assertException(error, {badmatch, []}, load_certificate(CertPath)),
    ?assertEqual([{CertPath, []}], ets:lookup(esaml_certbin_cache, CertPath)).

-include("xmerl_xpath_macros.hrl").

-record(b, {name, ctext}).

xpath_attr_test() ->
    {Xml, _} = xmerl_scan:string("<a><b name=\"foo\"><c name=\"bar\">hi</c></b><b name=\"foobar\"><c name=\"foofoo\"></c></b></a>", [{namespace_conformant, true}]),
    Ns = [],
    Fun = ?xpath_attr("/a/b[@name='foo']/c/@name", b, name),
    Rec = Fun(#b{}),
    ?assertMatch(#b{name = "bar"}, Rec),
    Fun2 = ?xpath_attr("/a/b[@name='foobar']/c/@name", b, name),
    Rec2 = Fun2(Rec),
    ?assertMatch(#b{name = "foofoo"}, Rec2),
    Fun3 = ?xpath_attr("/a/b[@name='bar']/c/@name", b, name),
    Rec3 = Fun3(Rec2),
    ?assertMatch(Rec2, Rec3).

xpath_attr_trans_test() ->
    {Xml, _} = xmerl_scan:string("<a><b name=\"foo\"><c name=\"bar\">hi</c></b><b name=\"foobar\"><c name=\"foofoo\"></c></b></a>", [{namespace_conformant, true}]),
    Ns = [],
    Fun = ?xpath_attr("/a/b[@name='foobar']/c/@name", b, name, fun(X) -> list_to_atom(X) end),
    Rec = Fun(#b{}),
    ?assertMatch(#b{name = foofoo}, Rec).

xpath_text_test() ->
    {Xml, _} = xmerl_scan:string("<a><b name=\"foo\"><c name=\"bar\">hi</c></b><b name=\"foobar\"><c name=\"foofoo\"></c></b></a>", [{namespace_conformant, true}]),
    Ns = [],
    Fun = ?xpath_text("/a/b[@name='foo']/c/text()", b, ctext),
    Rec = Fun(#b{}),
    ?assertMatch(#b{ctext = "hi"}, Rec),
    Fun2 = ?xpath_text("/a/b[@name='foobar']/c/text()", b, ctext),
    Rec2 = Fun2(Rec),
    ?assertMatch(Rec, Rec2),
    Fun3 = ?xpath_text("/a/b[@name='bar']/c/text()", b, name),
    Rec3 = Fun3(Rec2),
    ?assertMatch(Rec2, Rec3).

-endif.
