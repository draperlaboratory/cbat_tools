




function sum_array(mem: array<int>, start: int, end:int): int
requires start >= 0
requires end <= mem.Length
decreases end - start
reads mem
{
  if start >= end then
    0
  else
    mem[start] + sum_array(mem, start + 1, end)
}

method Sum(length: int, mem: array<int>) returns (total: int)
requires length <= mem.Length
ensures total == sum_array(mem, 0, length)
{
  var n := 0;
  total := 0;

  while(n < length)
  invariant sum_array(mem, 0, length) ==
  (total + sum_array(mem, n, length))
  {
    total := total + mem[n];
    n := n + 1;
  }

}
