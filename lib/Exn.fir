prim throw(exn: exn) a / exn

prim try(cb: Fn() a / exn) Result[exn, a]

untry(res: Result[exn, a]) a / exn:
    match res:
        Result.Ok(a): a
        Result.Err(err): throw(err)
