# This is generated file, do not edit.

import Peg.ParseTree
import Token

type_(tokens: Vec[Token], cursor: U32) (tree: Type, newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let nonTerminalResult = namedType(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let t = nonTerminalResult.tree
        let value = do:
            Type.Named(t)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let id = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LowerId, ..)):
            let sym = tokens.get(cursor)
            cursor += 1
            sym
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            Type.Var(newId(id.text))
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))

namedType(tokens: Vec[Token], cursor: U32) (tree: NamedType, newCursor: U32, newErr: Option[ParseError]) / ParseError:
    let cursor0 = cursor
    let curErr: Option[ParseError] = Option.None
    let altResult = try(||:
        let name = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.UpperId, ..)):
            let sym = tokens.get(cursor)
            cursor += 1
            sym
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.LBracket, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let nonTerminalResult = type_(tokens, cursor)
        cursor = nonTerminalResult.newCursor
        curErr = nonTerminalResult.newErr
        let arg0 = nonTerminalResult.tree
        let args = Vec.empty()
        loop:
            let symResult = try(||:
                if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
                    cursor += 1
                else:
                    throw(
                        ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
                let nonTerminalResult = type_(tokens, cursor)
                cursor = nonTerminalResult.newCursor
                curErr = nonTerminalResult.newErr
                let t = nonTerminalResult.tree
                args.push((t = t))
                (cursor = cursor, err = curErr)
            )
            match symResult:
                Result.Err(err):
                    curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
                    break
                Result.Ok(ok):
                    cursor = ok.cursor
                    curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        let symResult = try(||:
            if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.Comma, ..)):
                cursor += 1
            else:
                throw(
                    ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
            (cursor = cursor, err = curErr)
        )
        match symResult:
            Result.Err(err):
                curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            Result.Ok(ok):
                cursor = ok.cursor
                curErr = ParseError.takeAdvancedOpt(curErr, ok.err)
        if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.RBracket, ..)):
            cursor += 1
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            let args = once(arg0).chain(args.iter().map(|arg: (t: Type)|: arg.t)).toVec()
            NamedType(name = newId(name.text), args = args)
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    let altResult = try(||:
        let name = if tokens.getOpt(cursor) is Option.Some(Token(kind = TokenKind.UpperId, ..)):
            let sym = tokens.get(cursor)
            cursor += 1
            sym
        else:
            throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
        let value = do:
            NamedType(name = newId(name.text), args = Vec.empty())
        (value = value, cursor = cursor, err = curErr)
    )
    match altResult:
        Result.Err(err):
            curErr = Option.Some(ParseError.takeAdvanced(curErr, err))
            cursor = cursor0
        Result.Ok((value = value, cursor = newCursor, err = newErr)):
            return (tree = value, newCursor = newCursor, newErr = newErr)
    throw(ParseError.takeAdvanced(curErr, ParseError(cursor = cursor)))
