method isPrefix(pre: string, str: string) returns (res:bool)
{
 var i := 0; 
 while i < |pre| && i < |str|
 invariant i >= 0; 
 {
  if pre[i] != str[i]
  {
    return false;
  }
  i := i + 1; 
 } 
 return true;
}

method isSubstring(sub: string, str: string) returns (res:bool)
{
 var i := 0;
 while i < |str|
 {
  var isSub := isPrefix(sub,str[i..]);
  if isSub == true { return true; }
  else { i := i + 1; } 
 }
 return false;
}

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
{

}

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
{

}
