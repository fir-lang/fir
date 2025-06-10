trait Sequence[seq, t, exn]:
    forEach(self: seq, consumer: Fn(t) / exn) / exn

# ------------------------------------------------------------------------------

type CountFrom:
    from: U32

impl Sequence[CountFrom, U32, exn]:
    forEach(self: CountFrom, consumer: Fn(U32) / exn) / exn:
        let i = self.from
        loop:
            consumer(i)
            i += 1

# ------------------------------------------------------------------------------

type AppendAfter[s1, s2]:
    seq1: s1
    seq2: s2
    amt: U32

type AppendAfterStop:
    AppendAfterStop

impl[Sequence[s1, t, [AppendAfterStop, ..exn]], Sequence[s2, t, [AppendAfterStop, ..exn]]]
        Sequence[AppendAfter[s1, s2], t, [AppendAfterStop, ..exn]]:
    forEach(
            self: AppendAfter[s1, s2],
            consumer: Fn(t) / [AppendAfterStop, ..exn]
        ) / [AppendAfterStop, ..exn]:
        match try({
            self.seq1.forEach(fn(i: t) / [AppendAfterStop, ..exn] {
                if self.amt == 0:
                    throw(~AppendAfterStop.AppendAfterStop)
                self.amt -= 1
                consumer(i)
            })
        }):
            Result.Ok(()) | Result.Err(~AppendAfterStop.AppendAfterStop):
                self.seq2.forEach(consumer)

# ------------------------------------------------------------------------------

type EmptySeq:
    EmptySeq

impl Sequence[EmptySeq, t, exn]:
    forEach(self: EmptySeq, consumer: Fn(t) / exn) / exn:
        ()

# ------------------------------------------------------------------------------

main():
    let seq =
        AppendAfter(
            seq1 = AppendAfter(seq1 = CountFrom(from = 0), seq2 = CountFrom(from = 10), amt = 5),
            seq2 = EmptySeq.EmptySeq,
            amt = 5,
        )

    try[[AppendAfterStop], (), []]({
        seq.forEach(fn(i: U32) {
            print(i)
        })
    })

    ()

# expected stdout:
# 0
# 1
# 2
# 3
# 4

# expected stderr: tests/Issue137_4.fir:32:9: Unexhaustive pattern match

