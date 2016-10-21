// The Prisoner of Benda
//
// The array L represents a permutation of the minds of the crew, where index i
// is body i and contains mind L[i]. Without loss of generality (since an 
// invertable data transformer exists for any list), assume that minds and
// bodies are numbered 0 through L.Length. So originally body i had mind i.
//
// Prove that the following algorithm correctly switches everyone back,
// including the two extra bodies.
//
// The algorithm is outlined at:
//
//   https://en.wikipedia.org/wiki/The_Prisoner_of_Benda

method benda(L:array<int>, v0:int, v1:int) returns (x:int, y:int)
  // Do no change these.
  requires L != null;
  requires forall i::0 <= i < L.Length ==> 0 <= L[i] < L.Length; // in range
  requires forall i,j::0 <= i < j < L.Length ==> L[i] != L[j]; // distinct
  requires v0 !in L[..] && v1 !in L[..] && v0 != v1;
  modifies L;
  ensures forall j::0 <= j < L.Length ==> L[j] == j; // everyone is switched back
  ensures x == v0 && y == v1; // extras are also switched back
{
  var i;
  i,x,y := 0,v0,v1;
  while (i < L.Length)
    // You must provide appropriate loop invariants here
    invariant 0 <= i <= L.Length
    //invariant forall J::0 <= j < L.Length
    // we want to do this but this might be too simple 
    //invariant forall k::0 <= k < i ==> L[k] == k
    invariant forall d::0 <= d < L.Length ==> 0 <= L[d] < L.Length
    //invariant (x != v0) ==> (x == y && y == x)
    //invariant (x == v0 && y == v1) || (x == v1 && y == v0)
    invariant forall k::0 <= k < i && k < L.Length ==> x != L[k] 
    invariant forall k::0 < k < i ==> L[k] in (set z | i < z < L.Length && L[z] != z)
    invariant x == v0 && y == v1 
    // invariant y == v1 && x == v0 ==> x == v0
    {       
    if (L[i] != i) { // if mind of i does not match with body i
      x,L[i] := L[i],x; // swap mind between i and x

      // Uses x and y to help swap one cycle back to identity without 
      // swapping (x,y).
      // Detailed explainations can be found at: 
      // https://en.wikipedia.org/wiki/The_Prisoner_of_Benda (The proof).
      x := cycle(L,i,x,(set z | i < z < L.Length && L[z] != z));

      y,L[x] := L[x],y; // swap minds between y and x
      x,L[x] := L[x],x; // put mind of x back to its body
      y,L[i] := L[i],y; // swap minds between y and i 
    }
    i := i+1;
  }

  // If the two extras are switched at the end, switch back.
  if (x != v0) {
    x,y := y,x;
  } 
}

// Put a cycle permutation back to identity permutation.
// https://en.wikipedia.org/wiki/Cyclic_permutation
method cycle(L:array<int>, i:int, a:int, s:set<int>) returns (x:int)
  // You must provide appropriate pre-conditions here.
  requires L != null
 
  modifies L
  decreases s
  requires 0 <= i < L.Length 
  // does the x L[x] swap make sure x is still in range?  
  //ensures forall d::0 <= d < L.Length ==> 0 <= L[d] < L.Length
  requires forall c:: i < c < L.Length && L[c] != c ==> c in s
  requires 0 <= a < L.Length && a <= L[a] < L.Length && L[a] != i && s != {}
  //requires 0 <= a < L.Lengthi
  requires 0 <= L[a] < L.Length
  requires a in s && s - {a} < s   
  //  requires forall c:: i in s ==> i in L[..]
  // You must provide appropriate post-conditions here.
  ensures 0 <= x < L.Length
  ensures L[x] == i 
//  ensures L[a] == i ==> x == a
  
{ 
  x := a;
  if (L[x] != i) { // mind and body do not match.
    x,L[x] := L[x],x;
    x := cycle(L,i,x,s-{a});
  }
}

method Main()
{
  var a:= new int[5];
  a[0],a[1],a[2],a[3],a[4]:= 3,2,1,4,0;
  var x,y:= benda(a, a.Length, a.Length + 1);
  print a[..]," ",x," ",y,"\n";
}
