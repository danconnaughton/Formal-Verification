method isPrefix(pre: string, str: string) returns (res:bool)
{
 var i := 0;
 if |pre| > |str|
 {
	return false;
 } 
 while i < |str| && i < |pre|
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
  var i := 0;
  while i <= (|str1|-k)
  {
    var isSub := isSubstring(str1[i..i+k], str2);
	if isSub == true { return true;}
	else {i := i + 1;}
  }
  return false;
}

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
{
  var i := 1;
  while i <= |str1| && i <= |str2|
  {
    var hasCommon := haveCommonKSubstring(i, str1, str2);
    if(hasCommon == false){ return i-1;}
    i := i+1;
  }
  return i-1;
}
