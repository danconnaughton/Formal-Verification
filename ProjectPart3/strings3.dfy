predicate isPrefixPred(pre:string, str:string)
{
	(|pre| <= |str|) && 
	pre == str[..|pre|]
}

predicate isNotPrefixPred(pre:string, str:string)
{
	(|pre| > |str|) || 
	pre != str[..|pre|]
}

lemma PrefixNegationLemma(pre:string, str:string)
	ensures  isPrefixPred(pre,str) <==> !isNotPrefixPred(pre,str)
	ensures !isPrefixPred(pre,str) <==>  isNotPrefixPred(pre,str)
{}

method isPrefix(pre: string, str: string) returns (res:bool)
	ensures !res <==> isNotPrefixPred(pre,str)
	ensures  res <==> isPrefixPred(pre,str)
{
 
 if |pre| > |str| { return false; }
 
 var i := 0;
 res := true;

 while(i < |pre| && res )
	decreases |pre| - i + (if res then 1 else 0)
	invariant 0 <= i <= |pre|;
	invariant res ==> isPrefixPred(pre[..i],str) 
	invariant !res ==> !isPrefixPred(pre,str)
	{
		if pre[i] != str[i]
		{
			res := false;
		}
		else
		{
			i := i + 1;
		} 
	}	 
}
predicate isSubstringPred(sub:string, str:string)
{
	(exists i :: 0 <= i <= |str| &&  isPrefixPred(sub, str[i..]))
}

predicate isNotSubstringPred(sub:string, str:string)
{
	(forall i :: 0 <= i <= |str| ==> isNotPrefixPred(sub,str[i..]))
}

lemma SubstringNegationLemma(sub:string, str:string)
	ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
	ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
{}

method isSubstring(sub: string, str: string) returns (res:bool)
	ensures  res <==> isSubstringPred(sub, str)
	//ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
{
  if(|sub|>|str|){return false;}
  var i := 0;
  res := false;
 while i+|sub| < |str| && !res
 decreases |str| - i + (if res then 0 else 1)
 invariant 0 <= (i+|sub|) <= |str|
 invariant res ==> isSubstringPred(sub, str)
 invariant !res ==> !isSubstringPred(sub, str[..|sub|+i])
 {
  var isSub := isPrefix(sub,str[i..]);
  if isSub == true { res:= true; }
  else { i := i + 1; } 
 }
}


predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	exists i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k && isSubstringPred(str1[i1..j1],str2)
}

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	forall i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k ==>  isNotSubstringPred(str1[i1..j1],str2)
}

lemma commonKSubstringLemma(k:nat, str1:string, str2:string)
	ensures  haveCommonKSubstringPred(k,str1,str2) <==> !haveNotCommonKSubstringPred(k,str1,str2)
	ensures !haveCommonKSubstringPred(k,str1,str2) <==>  haveNotCommonKSubstringPred(k,str1,str2)
{}

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
	ensures found  <==>  haveCommonKSubstringPred(k,str1,str2)
	//ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
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
	requires (|str1| <= |str2|)
	ensures (forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2))
	ensures haveCommonKSubstringPred(len,str1,str2)
{
var i := 1;
  while i <= |str1| && i <= |str2|
  {
    var hasCommon := haveCommonKSubstring(i, str1, str2);
    if(hasCommon == false){ return i-1;}
    i := i+1;
  }
  return i-1;}


