import macros
import strutils
import json

macro dumpAst(e: untyped): stmt =
    echo treeRepr(e)

proc newQuoteExpr(content: NimNode): NimNode {.compileTime.} =
    let doNode = newNimNode(nnkDo).add(newEmptyNode(), newEmptyNode(), newEmptyNode(), newEmptyNode(), newEmptyNode(), newEmptyNode(), content)
    result = newCall(newIdentNode("quote"), doNode)

proc newPragmaCompileTime(): NimNode {.compileTime.} =
    newNimNode(nnkPragma).add(newIdentNode("compileTime"))

proc newParamDecl(symOrIdent: NimNode, typ: NimNode): NimNode {.compileTime.} =
    result = newNimNode(nnkIdentDefs).add(symOrIdent, typ, newEmptyNode())

macro restInterface(e: expr, s: untyped): stmt =
    let pragmaExpr = newNimNode(nnkPragmaExpr).add(newIdentNode($e & "AST"), newPragmaCompileTime())
    result = newNimNode(nnkLetSection).add(newNimNode(nnkIdentDefs).add(pragmaExpr, newEmptyNode(), newQuoteExpr(s)))

proc genRestClientType(clientTypeName: string, body: NimNode): NimNode {.compileTime.} =
    result = newNimNode(nnkTypeSection).add(newNimNode(nnkTypeDef).add(newIdentNode(clientTypeName), newEmptyNode(), newNimNode(nnkObjectTy).add(newEmptyNode(), newEmptyNode(), newEmptyNode())))

proc getPragmaValue(d: NimNode, key: string): NimNode {.compileTime.} =
    for i in d.pragma:
        if i.kind == nnkExprColonExpr and $(i[0]) == key:
            return i[1]

proc expandProcParams(formalParamsNode: NimNode): NimNode {.compileTime.} =
    result = newNimNode(nnkFormalParams)
    for i in 1 ..< formalParamsNode.len:
        if formalParamsNode[i].kind == nnkIdentDefs:
            for j in 0 ..< formalParamsNode[i].len - 2:
                result.add(newParamDecl(formalParamsNode[i][j], formalParamsNode[i][^2]))

proc genURLFormatBracketForProc(d: NimNode): NimNode {.compileTime.} =
    result = newNimNode(nnkBracket)
    for i in expandProcParams(d.params):
        result.add(newStrLitNode($(i[0])), i[0])

proc genMakeHTTPRequestProc(d: NimNode, clientTypeName: string): NimNode {.compileTime.} =
    let clientSym = genSym(nskParam, "client")
    result = newProc(newIdentNode("makeHTTPRequestFor" & $(d[0])), [newIdentNode("HTTPRequest"), newParamDecl(clientSym, newIdentNode(clientTypeName))])
    for i in 1 ..< d.params.len:
        result.params.add(d.params[i])
    result.body = newStmtList()
    let urlFormat = $(getPragmaValue(d, "url"))
    result.body.add(newAssignment(
        newDotExpr(newIdentNode("result"), newIdentNode("url")),
        newNimNode(nnkInfix).add(newIdentNode("%"), newStrLitNode(urlFormat), genURLFormatBracketForProc(d))
        ))

    result.body.add(newAssignment(
        newDotExpr(newIdentNode("result"), newIdentNode("httpMethod")),
        copyNimTree(getPragmaValue(d, "httpMethod"))
        ))

    result.body.add(newAssignment(
        newDotExpr(newIdentNode("result"), newIdentNode("body")),
        prefix(prefix(copyNimTree(getPragmaValue(d, "reqBody")), "%*"), "$")
        ))

proc genResultHandlingClosure(d: NimNode, handlerIdent: NimNode): NimNode {.compileTime.} =
    let respIdent = newIdentNode("response")
    result = newProc(newIdentNode("handleResponse"), [newEmptyNode(), newParamDecl(respIdent, newIdentNode("HTTPResponse"))])
    let reqBodyDesc = getPragmaValue(d, "respBody")
    let handlerCall = newCall(handlerIdent)
    if reqBodyDesc.kind == nnkTableConstr:
        # Response is json
        result.body.add(newLetStmt(newIdentNode("parsedJson"), newCall(newIdentNode("parseJson"), newDotExpr(respIdent, newIdentNode("body")))))
    else:
        handlerCall.add(newDotExpr(respIdent, newIdentNode("body")))
    result.body.add(handlerCall)

proc genHandlerTypeFromResultType(res: NimNode): NimNode {.compileTime.} =
    let formalParamsNode = newNimNode(nnkFormalParams).add(newEmptyNode())
    if res.kind == nnkTupleTy:
        discard
    else:
        formalParamsNode.add(newParamDecl(newIdentNode("r"), copyNimTree(res)))

    result = newNimNode(nnkProcTy).add(formalParamsNode, newEmptyNode())

proc genClientProcForDeclaration(d: NimNode, clientTypeName: string, requestProcSym: NimNode): NimNode {.compileTime.} =
    result = newStmtList()
    let makeRequestProc = genMakeHTTPRequestProc(d, clientTypeName)
    result.add(makeRequestProc)

    let clientSym = genSym(nskParam, "client")

    let makeRequestCall = newCall(makeRequestProc[0], clientSym)

    let targetProc = newProc(copyNimTree(d[0]), [newEmptyNode(), newParamDecl(clientSym, newIdentNode(clientTypeName))])

    for n in expandProcParams(d.params):
        let argSym = newIdentNode($n [0])
        makeRequestCall.add(argSym)
        targetProc.params.add(newParamDecl(argSym, copyNimTree(n[1])))

    let handlerIdent = newIdentNode("handler")
    targetProc.params.add(newParamDecl(handlerIdent, genHandlerTypeFromResultType(d.params[0])))

    let responseHandlingProc = genResultHandlingClosure(d, handlerIdent)

    targetProc.body.add(responseHandlingProc, newCall(requestProcSym, makeRequestCall, responseHandlingProc[0]))
    result.add(targetProc)

proc getSendAsyncRequestImpl(body: NimNode): NimNode {.compileTime.} =
    result = body.findChild(it.kind == nnkProcDef and $(it[0]) == "sendRestHTTPRequestAsync")
    if not result.isNil:
        result = copyNimTree(result)
        result[0] = genSym(nskProc, "sendRestHTTPRequestAsync")

proc getRestInterfaceImplementationForAST(a: NimNode, body: NimNode, clientTypeName: string): NimNode {.compileTime.} =
    result = newStmtList()
    let sendAsyncProc = getSendAsyncRequestImpl(body)
    result.add(sendAsyncProc)
    result.add(genRestClientType(clientTypeName, body))
    echo clientTypeName

    for n in a:
        result.add(genClientProcForDeclaration(n, clientTypeName, sendAsyncProc[0]))
    echo "CLIENT_RESULT: ", treeRepr(result)

type HTTPRequest = object
    url: string
    httpMethod: string
    body: string

type HTTPResponse = object
    statusCode: int
    status: string
    body: string

proc newMacro*(name = newEmptyNode(); params: openArray[NimNode] = [newEmptyNode()];
    body: NimNode = newStmtList()): NimNode {.compileTime.} =
  ## shortcut for creating a new proc
  ##
  ## The ``params`` array must start with the return type of the proc,
  ## followed by a list of IdentDefs which specify the params.
  result = newNimNode(nnkMacroDef).add(
    name,
    newEmptyNode(),
    newEmptyNode(),
    newNimNode(nnkFormalParams).add(params), ##params
    newEmptyNode(),  ## pragmas
    newEmptyNode(),
    body)

macro restClient(e: expr): stmt =
    let clientTypeName = e[1]
    let interfaceTypeName = e[2]
    result = newStmtList()
    result.add(newMacro(newIdentNode($interfaceTypeName & "ImplementClient"), [newIdentNode("stmt")], newStmtList().add(newCall(newIdentNode("getRestInterfaceImplementationForAST"), newIdentNode($interfaceTypeName & "AST"),
        newNilLit(),
        newStrLitNode($clientTypeName)))))
    result.add(newCall(newIdentNode($interfaceTypeName & "ImplementClient")))

macro restClient(e: untyped, body: untyped): stmt =
    let clientTypeName = e[1]
    let interfaceTypeName = e[2]
    result = newStmtList()
    result.add(newMacro(newIdentNode($interfaceTypeName & "ImplementClient"), [newIdentNode("stmt")], newStmtList().add(newCall(newIdentNode("getRestInterfaceImplementationForAST"), newIdentNode($interfaceTypeName & "AST"),
        newQuoteExpr(body),
        newStrLitNode($clientTypeName)))))
    result.add(newCall(newIdentNode($interfaceTypeName & "ImplementClient")))

when true:
    restInterface FacebookRestInterface:
        proc login(name, pass: string): string {.
            url: "/login/$name"
            httpMethod: "POST"
            reqBody: {"name": name, "pass": pass}
            respBody: result
            .}

    restClient FacebookRestClient of FacebookRestInterface:
        proc sendRestHTTPRequestAsync(req: HTTPRequest, handler: proc(res: HTTPResponse)) =
            echo "Sending request: ", req
            var resp: HTTPResponse
            resp.body = "YO!!!"
            handler(resp)

    var cl: FacebookRestClient
    cl.login "yglukhov", "1234", proc(r: string) =
        echo "RESPONSE: ", r

else:
    dumpAst:
        var re: HTTPRequest
        proc a(asdf: proc(a, b: int))
