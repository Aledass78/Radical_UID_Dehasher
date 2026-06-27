#include "vector"
#include "fstream"
#include "sstream"
#include "cmath"

using namespace std;


//Global Vars
char * symbols;
size_t symbols_size = -1;


__int64 MakeUID(const char *x)
{
if (!x)
return 0;

__int64 h = 0;
char* s = (char*)x;
while(*s)
{
h *= 65599;
h = (h ^ *s);
++s;
}
return h;
}

//This thing adds unique value in vector.
//I did'nt wanna use std::find, because i dodn't wanna include "algorithm"
//Dumb idea.
bool Check_UniqeValue_Vector(std::vector<__int64>& vec, __int64 value){
    bool found = false;
    for (__int64 existingValue : vec) {
        if (existingValue == value) {
            found = true; break;}}
    return !found; //Return true if there's no same value in vector.
}

//I don't wanna comment it.
//Bad code.
void Settings_File_Reader(){ //Just for symbols in the current interpretation.
fstream File("settings.txt", ios::in | ios::out);
if(!File.is_open()){
cout << "Can't Open \"settings.txt\" File.\n";
system("pause");
}



size_t pos = 0;
string line;                //Read file
while(getline(File, line)){ //Line by line
                            //To get the settings

if ((line.find("Symbols:")) != std::string::npos){//Use switch in future.
vector <char> Victor_Char; //Say hello to our collector.
pos = 7; //Dumb but simple

do{ //do while because of Dumb but simple
pos++;
Victor_Char.push_back(line.substr(pos, 1)[0]);
}while((pos = line.find(",", pos)) != std::string::npos);


    delete[] symbols;                                       
	symbols = new char[Victor_Char.size() + 1];
    for(int i = 0; i < Victor_Char.size(); i++, symbols_size++) symbols[i] = Victor_Char[i];//copy the stuff & count the sizeof symbols
    symbols[Victor_Char.size()] = 0;
} //An idiot admires complexity, a genius admires simplicity 



}//file read while

}



//This function reads UID from FILE. It looks for "0x" and then reads 16 symbols next to it.
//For some fuckin reason i can't just read hex value even with unsigned long long & std::hex, so we have what we have. Conversion.
//TODO: Figure out what went wrong and rewrite it.
//Also bad code ahead.
void UID_Reader(vector <__int64> & uids, vector <string> & uids_names){
//Open FILE both read & write.
fstream FILE("uids.txt", ios::in | ios::out);

//if we failed to open our FILE, send to the user's console polite message of confusion. :)
    if(!FILE.is_open()){ 
        cout << "My Nigga, im trying to open file \"uids.txt\" in read & write mode...\n Why can't i open it?\n";
		system("pause");
        return;        }
                       
//Now, we read FILE line by line 
        string line;
            while (std::getline(FILE, line)){
                
                /*//Here we're trying to find our uids.
                We need to look for "0x" which means start of UID, then we must take next 16 symbols.
                */


                size_t pos = 0; //line position
                while ((pos = line.find("0x", pos)) != std::string::npos) { //if there are a "0x" in the line
                    // Found "0x", get our hex.
                    std::istringstream hexValueStream(line.substr(pos + 2, 16)); //pos + 2 & 16 since we getting 16 symbols after "0x".
						 //Because stringstream act strange with signed long long.
				         //We convert it to unsigned long long, and then to signed long long
                        unsigned long long hexValue;
                        hexValueStream >> std::hex >> hexValue;
                        __int64 intValue = hexValue;

                     if(Check_UniqeValue_Vector(uids, intValue)){     //If we have NOT same UID in our UID vector.
					uids.       push_back(intValue);            //We add new UID in our UID vector.
                    uids_names. push_back(line.substr(pos, 18)); //It's text version of an UID.
					                       }
                    
                    // And we remove current UID from the line, so we will not find it again.
                    line.erase(pos, 18); //18 since we delete with "0x"
                                                                            }


                                             }    
//Close the file.
FILE.close();



return;
}


//I was lazy. Done by AI.
void Replace_Text_In_File(const std::string& filePath, const std::string& searchStr, const std::string& replaceStr) {
    std::ifstream inputFile(filePath);
    if (!inputFile.is_open()) {
        std::cerr << "Unable to open input file: " << filePath << std::endl;
        return;
    }

    // Чтение содержимого файла в строку
    std::ostringstream contentStream;
    contentStream << inputFile.rdbuf();
    std::string fileContent = contentStream.str();
    inputFile.close();

    // Поиск и замена текста
    size_t pos = fileContent.find(searchStr);
    while (pos != std::string::npos) {
        fileContent.replace(pos, searchStr.length(), replaceStr);
        pos = fileContent.find(searchStr, pos + replaceStr.length());
    }

    // Запись измененного содержимого обратно в файл
    std::ofstream outputFile(filePath);
    if (!outputFile.is_open()) {
        std::cerr << "Unable to open output file: " << filePath << std::endl;
        return;
    }

    outputFile << fileContent;
    outputFile.close();
}












//We need to consider all combinations.
size_t calculate_iteration_amount(size_t length_of_symbols, size_t length_of_small_xor_string){
   
    length_of_small_xor_string -= 1; //there's '\0' at the end of small_xor_string
	
	size_t result = 0;
for (size_t i = length_of_small_xor_string; i > 0; i--)
	result += pow(length_of_symbols, i);


return result;
}













//Ah here we go. Four Sybol Long UID Dehaser.
//This is a 17th version of this function.
//Previous ones either had speed problems or was unreadable at all.
//This is a perfect combination of speed and readability	.
// THIS FUNCTION IS MORE EFFICIENT THAN JUST LET'S SAY 12 CYCLES. AND MORE MANAGEABLE.

// Why is it so compact? Couldn't everything be distributed among functions?
// Function call is a jump. Jump is an instruction. And here we talking about 50.000.000 UID/sec. And i wanted this to be as fast as possible.
// What about inline? Inline is just an ask to the compiler: would you so kindly make this function inline? Read gcc.cpp for more info about inline.

//What's this function do? Brute-Force UID. BUT ONLY 4 SYMBOLS LONG It's simple.
//There are three variables:
// global symbols char pointer that contains symbols we wanna use in dehasher.
//                                           why do we wanna use different symbols? Less symbols = less iterations = more symols that we can dehash.
//                                           We will dehash more UID, if we will not use not frequent letters & uppercases.
// Curr_UID where we calculate our UID from small_xor_string.
// small_xor_string and their helping stuff which we use to generate our strings
//    ================================= HOW IT'S WORKING =========================================
// 0. Preparations. We calculate how many iteration we'll need with current amount of symbols and current small_xor_string lengh.
// 1.In small_xor_string we produce our strings from global symbols char*:
//   - We start from 0 element in small_xor_string. //1st element.
//   - We check if it's last element //When symbols are "a,b,c,d,e" we check if First element is "e".
//   - If it is, then we set our symbol to the first of the symbols, and proceed to the next element in small_xor_string
//   - If it's not, then just step to the next symbol in array.
//      C implementation of Assembler Brute Force.
// 2. We generate UID from created string
//curr_UID = (curr_UID << 16) - curr_UID + (curr_UID << 6) ^ *iterator; //Here same thing happens as in MakeUID().
// 3. Just compare UIDs. Simple.
// 4. It will stop the loop when small_xor_string will be 5 symbols long.


void four_symbol_long_UID_Dehasher(vector <__int64>& Uids, vector <string>& Uid_Names){ //Long story short.
	
//__int64 and long long have same size;

long long curr_UID = 0;



char small_xor_string[5] = {0,0,0,0,0}; //Here our three symbols. There they are.
int small_xor_string_pos[5] = {-1,-1,-1,-1};
char *small_xor_string_end_ptr = small_xor_string + sizeof(small_xor_string) - 2;
size_t small_xor_string_size = sizeof(small_xor_string) - 1;


size_t small_xor_iteration_amount = calculate_iteration_amount(sizeof(symbols), sizeof(small_xor_string));




//
int v = 0;
while(small_xor_string[4] == 0){

for(int i = 0; i != small_xor_iteration_amount; i++  ){ //Not_eq should be fastest

v = 0;

small_check_back:
if (small_xor_string[v] == symbols[symbols_size]){
small_xor_string[v]=symbols[0];
small_xor_string_pos[v] = 0;
v++;
goto small_check_back;
} // (word generator if) 



else{
small_xor_string_pos[v]++;
small_xor_string[v] = symbols[small_xor_string_pos[v]];

/////////////////////////////////////
/*Here UID xor logic*/
curr_UID = 0;
for (char * iterator = small_xor_string_end_ptr; iterator >= small_xor_string; iterator--) { //It's faster. But reconsider using it, since we read from iterator after.
	if (*iterator){ curr_UID = (curr_UID << 16) - curr_UID + (curr_UID << 6) ^ *iterator; }} //Here end of UID xor for & if)



//cout << "" << Uid_Names[0] << " 0x" << curr_UID << " " << small_xor_string<< "\n";
/*Here we check our UIDs*/
for (int i = Uids.size() - 1; i >= 0; i--) {
    if(Uids[i] == curr_UID){
		string reverser = small_xor_string;                 //Create string for reversing our array
		reverser.assign(reverser.rbegin(), reverser.rend());//Reverse string with reversed iterators
		
		cout << "Dehashed! UID: " << Uid_Names[i] << " means: " << reverser << "\n"; //std::hex & std::dec?
		Replace_Text_In_File("uids.txt", Uid_Names[i], reverser);
		Uids.erase(Uids.begin() + i);
		Uid_Names.erase(Uid_Names.begin() + i);
	}//if_(uid_check)
}//for____(uid_check)



}}}}


//This function restores three last bytes
bool Key_Restorer(__int64 Problem_UID, __int64 Target_UID, string & curr_str){//

  //Since we don't care about performance,Let's keep it readable.
	for(short i = 32; i <= 127; i ++)
	 for(short j = 32; j <= 127; j ++)
	  for(short k = 32; k <= 127; k ++){
		  __int64 Working_UID = Problem_UID;
	       
		   Working_UID *= 65599;
		   Working_UID = Working_UID xor i;
		   Working_UID *= 65599;
		   Working_UID = Working_UID xor j;
		   Working_UID *= 65599;
		   Working_UID = Working_UID xor k;
		   
		   if (Working_UID == Target_UID) { 
           curr_str+= {(char)i, (char)j, (char)k}; //c++11
		   return 1; }//if
        }//ijk for
	  
return 0;

}

//let's do everything proper atleast here.
void Dumb_Dictionary_method(vector <__int64>& Uids, vector <string>& Uid_Names){
fstream FILE("dictionary.txt", ios::in | ios::out);
string key_getter = "";
__int64 UID = 0;
size_t lines_amount = 0;


    if(!FILE.is_open()){ 
     cout << "Can't Open \"dictionary.txt\" file.\n";
	 system("pause");
     return;
	}


 while (std::getline(FILE, key_getter)){
	lines_amount++;
  UID = MakeUID(key_getter.c_str()); //whoops. Anyways.
       //for(__int64 Uid : Uids){ //
	   for(int i = Uids.size() - 1; i >= 0; i--){
	      if(UID == Uids[i]){
		     cout << "Dehashed! UID: " << Uid_Names[i] << " means: " << key_getter << "\n";
		     Replace_Text_In_File("uids.txt", Uid_Names[i], key_getter);
		     Uids.erase(Uids.begin() + i);
		     Uid_Names.erase(Uid_Names.begin() + i);
		  }//uid if
	   } //vector for
  }//file while

cout << "Dictionary method finished!\n\n Lines amount in Dictionary: " << lines_amount << "\n\n\n";

FILE.close();

}