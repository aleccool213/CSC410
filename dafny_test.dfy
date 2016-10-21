method Main()
{
assert {1} <= {1, 2};
var a:= new int[5];
a[0], a[1], a[2] := 6, 0, 1;
print (set z | 0 < z < a.Length && a[z] != z);
//assert {0, 1} - {2} < {0, 1};
}
