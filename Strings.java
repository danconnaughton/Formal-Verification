
public class Strings {
    public static boolean isPrefix(String pre, String str){
    	
    	 int i = 0;
    	 if (pre.length() > str.length())
    	 {
    		return false;
    	 } 
    	 while (i < str.length() && i < pre.length())
    	 {
    	  if (pre.toCharArray()[i] != str.toCharArray()[i])
    	  {
    	    return false;
    	  }
    	  i = i + 1; 
    	 } 
    	 return true;
    	
    }
    
    public static boolean isSubstring(String sub, String str)
    {
     int i = 0;
     while (i < str.length())
     {
      boolean isSub = isPrefix(sub, str.substring(i));
      if (isSub == true) { return true; }
      else { i = i + 1; } 
     }
     return false;
    }
    
    public static boolean haveCommonKSubstring(int k, String str1, String str2)
    {
      int i = 0;
      while (i <= (str1.length()-k))
      {
        boolean isSub = isSubstring(str1.substring(i, i+k), str2);
        
    	if (isSub == true) { return true;}
    	else {i = i + 1;}
      }
      return false;
    }
    public static int maxCommonSubstringLength(String str1, String str2)
    {
      int i = 1;
      while (i <= str1.length() && i <= str2.length())
      {
        boolean hasCommon = haveCommonKSubstring(i, str1, str2);
		System.out.println(hasCommon);
        if(hasCommon == false){ return i-1;}
        i = i+1;
      }
      return i-1;
    }
    
    
    
	public static void main(String[] args) {
		
		System.out.println(maxCommonSubstringLength("ugcajts", "catsr"));

	}

}
