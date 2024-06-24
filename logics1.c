/*
Team Members
1.Aryan Saluja - 2021A7PS2947H
2.Vansh Agrawal -2021A7PS2998H
3.Ninad Agrawal -2021A7PS2948H
4.Abhishek Joshi -2021A7PS2727H
*/



#include <stdio.h>  
#include <stdlib.h>
#include <string.h>


int lineno;
#define LS 10
#define RS 128
char proof[LS][RS]; 
char line[LS][RS];  
char tree[129];     ///array to store tree
char temp[100];     ///array to temporarily store infix
int tog;            
int flag=0;

void treetoinfix(int i)    //trying to print right sub-tree
{   
    if (tree[i] != NULL) /// statements to follow to inorder taversal in a v=binary parse tree
    {  if(tree[(2*i)]!=NULL){
           
            temp[flag++]='(';
    }
        

        treetoinfix(2 * i);       /// first go to the left branch
        
        temp[flag++]=tree[i];
          /// print the value of the respective node
        treetoinfix((2 * i) + 1); /// then go to the right branch
        if(tree[(2*i+1)]!=NULL){
        
        temp[flag++]=')';}
    }
}

void infixtotree(char *a) /// convert infix to parse tree
{
    
    int l = strlen(a);
    int workid = 1;
    for (int i = 0; i <= l; i++)
    {
        if (a[i] == '(') /// if you see a '('
        {
            workid = workid * 2; /// move to the next level down from the current node
        }
        else if (a[i] == ')') /// if you see ')'
        {
            workid = workid / 2; /// move to the level up from the current node
        }
        else if ((a[i] >= 65 && a[i] <= 90) || (a[i] >= 97 && a[i] <= 122)) /// if there is any alphabet
        {
                       /// no of atoms is incremented
            tree[workid] = a[i]; /// update the array of tree elements
            workid = workid / 2; /// move to the level up from the current node
        }
        else if (a[i] == '~') /// in the case of a negation
        {
            workid = workid / 2;     /// move to the level up from the current node
            tree[workid] = a[i];     /// update the tree array
            workid = workid * 2 + 1; /// move to the right branch
        }
        else
        {
            tree[workid] = a[i];     /// update the tree array
            workid = workid * 2 + 1; /// move to the right branch
        }
    }
}

int andvalidity(char stmnt[], char a[] , char b[]){///AND INTRODUCTION RULE
    int ra = atoi(a);///integer storing the rule line number a
    int rb = atoi(b);///integer storing the rule line number b
    char chk[30] = {"("};
    strcat(chk , proof[ra]);///to check the proposition at line 'ra'
    strcat(chk , "^");      ///to check the "AND" propostion rule
    strcat(chk , proof[rb]);///to check the proposition at line 'rb'
    strcat(chk , ")");
    if(strcmp(chk,stmnt)==0) ///compare the computed "AND" rule with the given proof in the input
    return 1;                   
    return 0;
    
}


int implelimvalidity(char stmnt[] , char a[] , char b[]){///IMPLICATION ELIMINATION RULE
    int ra = atoi(a);///integer storing the rule line number a
    int rb = atoi(b); ///integer storing the rule line number b
    char chk[30] = {"("};
    strcat(chk , proof[rb]); ///to check the proposition at line 'rb'
    printf("\n%S",chk);
    strcat(chk , ">");///to check the "IMPLICATION" propositional rule
    printf("\n%S",chk);
    strcat(chk , stmnt);///to contcatenate the string stmnt to the string chk
    printf("\n%S",chk);
    strcat(chk , ")");
    printf("\n%S",chk);
    if(strcmp(chk,proof[ra])==0)///compare the resulting string chk to the input given
    return 1;
    return 0;
    
}


int modtolvalidity(char stmnt[] , char a[] , char b[]){///MODUS TOLLENS
    int ra = atoi(a);   ///integer storing the rule line number a
    int rb = atoi(b);   ///integer storing the rule line number b
    char tis1[30];
    char tis2[30];
    
    char chk[30] = {"("};
    for(int i = 0 ; i < 30 ; i++)
    tis1[i] = '\0';
    chk[0] = '(';

    
    memcpy(tis1,proof[rb]+2,strlen(proof[rb]+2) - 1);
    memcpy(tis2,stmnt+2,strlen(stmnt+2) - 1);
    printf("\n%s\n",chk);

    strcat(chk , tis2);
    printf("\n%s\n",chk);
    strcat(chk , ">");
    printf("\n%s\n",chk);

    strcat(chk , tis1);
    printf("\n%s\n",chk);
    
    int ok = (int)strlen(chk);
    
    strcat(chk , ")");
    printf("\n%s\n",chk);

    if(strcmp(chk,proof[ra])==0)
    return 1;
    return 0; 
}

int orintvalidity(char stmnt[],char a[],char b[]){///OR INTRODUCTION RULE
   // printf("%s\n",stmnt);
    int ra= atoi(a);        ///integer storing the rule line number a
    int rb= atoi(b);           ///integer storing the rule line number b
    infixtotree(stmnt);///convert the statement stmnt into a parsetree array making it easier for us to traverse the tree in any order of our choice
    
    if(ra==1) ///if the rule applicable to the first proposition in the rule
    {
        treetoinfix(2);  ///traverse the tree from the left branch from the top node
        if(strcmp(temp,proof[rb])==0)///compare the resulting proof to the input
        return 1;///compare the resulting proof to the input 
    }
    if(ra==2)   ///if the rule applicable to the second proposition in the rule
    {
        treetoinfix(3); ///traverse the tree from the right branch from the top node
        //printf("%s",temp);
        if(strcmp(temp,proof[rb])==0){///compare the resulting proof to the input
            return 1;
        }
        
        
    }
   
    return 0;
}


int andelvalidity(char stmnt[] , char a[] , char b[]){///AND ELIMINATION RULE
    int ra = atoi(a);       ///integer storing the rule line number a
    int rb = atoi(b);       ///integer storing the rule line number b
    flag=0;
    infixtotree(proof[rb]);  ///to check the validity of proposition at line no "rb"
    if(ra==1) ///if the rule applicable to the first proposition in the rule
    {
        treetoinfix(2); ///traverse the tree from the left branch from the top node
        if(strcmp(stmnt,temp)==0) ///compare the resulting proof to the input
        return 1;
    }
    if(ra==2) ///if the rule applicable to the second proposition in the rule
    {
    treetoinfix(3);///traverse the tree from the right branch from the top node
        if(strcmp(stmnt,temp)==0)///compare the resulting proof to the input
        return 1;
    }

    return 0;


}



int isvalid(char linei[],int count){
    
   char *token;
/// block to tokenize the given proof
   
   token = strtok(linei,"/");
   char* arg[4];    ///the given block of code would tokenize
   for(int j = 0 ; j < 4 ; j++)     /// the given conclusion into tokens wherein 
   arg[j] = '\0';                    /// our conclusive result, the rule used and  
   int jk = 0 ;                     ///the line numbers where the rule has been 
   while( token != NULL ) {             ///used would be treated as different tokens respectively   
      arg[jk] = token;
      jk++;
      token = strtok(NULL, "/");}           ///to differentiate everything in the conclusion of the proof
/// End of block

    
    printf("%s\n",arg[1]);          ///print the line number where the rule is applied
    
    
    if(*arg[1]=='P'){           ///if the rule is PREMISE
        return 1;
    }
    
    else if((arg[1][0] == 'a')  && (arg[1][1] == 'i')){ ///if the rule is AND INTROUDUCTION
       if(andvalidity(arg[0],arg[2],arg[3])){
       return 1;}
    }
    
    else if((arg[1][0] == 'i')  && (arg[1][1] == 'e')){ ///if the rule is IMPLICATION ELIMINATION
        
        if(implelimvalidity(arg[0],arg[2],arg[3])){
        return 1;}
    }
    
    else if((arg[1][0] == 'm')  && (arg[1][1] == 't')){ ///if the rule is MODUS TOLLENS
        
        if(modtolvalidity(arg[0],arg[2],arg[3])){
        return 1;}
    }
    else if((arg[1][0] == 'v')&& (arg[1][1] =='i')){    ///if the rule is OR INTRODUCTION
        if(orintvalidity(arg[0],arg[2],arg[3])){
            return 1;
        }
    }
    else if((arg[1][0]=='a')&& (arg[1][1]=='e')){       ///if the rule is AND ELIMINATION
        if(andelvalidity(arg[0],arg[2],arg[3]))
        return 1;
    }
    
    return 0;
    
}


int main ()
{
  FILE * fptr;
  FILE * infile;
  int i;
  int n=3;
  char str[100];
  char input[100];
  char str1;
  char * status1;
  int max = 0;
  int coun=0;
  
    
    printf("Enter N ");         ///enter the number of lines in the proof
	scanf("%d", &n);
	printf("\nEnter Proof\n");  ///enter the proof
	fptr = fopen ("test.txt","w"); 
	for(i = 0; i < n+1;i++)     ///The input that we give is give to a file opened in the above line
		{
		fgets(str, sizeof str, stdin);  ///standard input is taken into the string str
		fputs(str, fptr);           ///the string str in the file fptr
		}
    fclose (fptr);      ///close the file fptr
    
  
	char fname[20];
    
    i = 0;
    int tot = 0;
    
	strcpy(fname,"test.txt"); 

    fptr = fopen(fname, "r");
    while(fgets(line[i], RS, fptr)) 
	{
        line[i][strlen(line[i]) - 1] = '\0';
        i++;
    }
    tot = i;
	printf("\nThe content of the file %s  are : \n",fname);    
    for(i = 0; i < tot; ++i)
    {
        printf("%s\n", line[i]);
    }
    printf("\n");
    
    
    char cline[10][128];
    memcpy(cline,line,sizeof(char)*10*128);
    
    for(int k = 0 ;k < n ; k++){
    char *token;
    token = strtok(cline[k+1],"/");
    char arg[4][20];
    for(int j = 0 ; j < 4 ; j++)
    strcpy(arg[j] , "\0");
   
    int jk = 0 ;
   
    while( token != NULL ) {
      strcpy(arg[jk] , token);
      jk++;
      token = strtok(NULL, "/");}
      
      strcpy(proof[k+1] , arg[0]);
        
        
    }
    
    
    for(int h = 0 ; h < n ; h++){
        int ac = isvalid(line[h+1],h+1);

        if(ac==0){
        printf("Invalid");
        return 0;}
    }
    
    printf("Valid");
   


   return 0;
}


