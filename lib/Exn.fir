prim throw(exn: exn): exn a

prim try(cb: Fn(): exn a): Result[exn, a]

untry(res: Result[exn, a]): exn a
    match res:
        Result.Ok(a): a
        Result.Err(err): throw(err)
