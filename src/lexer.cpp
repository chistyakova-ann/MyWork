#include "../include/lexer.h"
#include "../include/get_init_state.h"
#include "../include/search_char.h"
#include "../include/belongs.h"
#include <set>
#include <string>
#include <vector>
#include "../include/operations_with_sets.h"
Lexer::Automaton_proc Lexer::procs[] = {
    &Lexer::start_proc(),     &Lexer::unknown_proc(),   
    &Lexer::idkeyword_proc(), &Lexer::delimiter_proc(), 
    &Lexer::string_proc()
};

Lexer::Final_proc Lexer::finals[] = {
    &Lexer::none_proc(),            &Lexer::unknown_final_proc(),   
    &Lexer::idkeyword_final_proc(), &Lexer::delimiter_final_proc(), 
    &Lexer::string_final_proc()
};

enum Category {
    SPACES,       DELIMITER_BEGIN, 
    STRING_BEGIN, IDKEYWORD_BEGIN, 
    IDKEYWORD0,   IDKEYWORD1,      
    IDKEYWORD2,   IDKEYWORD3,      
    Other
};

static const std::map<char32_t, uint8_t> categories_table = {
    {'\0', 1},   {'\X01', 1}, {'\X02', 1}, {'\X03', 1}, 
    {'\X04', 1}, {'\X05', 1}, {'\X06', 1}, {'\a', 1},   
    {'\b', 1},   {'\t', 1},   {'\n', 1},   {'\v', 1},   
    {'\f', 1},   {'\r', 1},   {'\X0e', 1}, {'\X0f', 1}, 
    {'\X10', 1}, {'\X11', 1}, {'\X12', 1}, {'\X13', 1}, 
    {'\X14', 1}, {'\X15', 1}, {'\X16', 1}, {'\X17', 1}, 
    {'\X18', 1}, {'\X19', 1}, {'\X1a', 1}, {'\X1b', 1}, 
    {'\X1c', 1}, {'\X1d', 1}, {'\X1e', 1}, {'\X1f', 1}, 
    {' ', 1},    {'!', 2},    {", 4},      {'#', 2},    
    {'%', 2},    {'&', 2},    {'(', 2},    {')', 2},    
    {'*', 2},    {'+', 2},    {',', 2},    {'-', 2},    
    {'/', 2},    {'0', 64},   {'1', 64},   {'2', 64},   
    {'3', 64},   {'4', 64},   {'5', 64},   {'6', 64},   
    {'7', 64},   {'8', 64},   {'9', 64},   {':', 2},    
    {';', 2},    {'<', 2},    {'=', 2},    {'>', 2},    
    {'?', 2},    {'A', 88},   {'B', 88},   {'C', 88},   
    {'D', 88},   {'E', 88},   {'F', 88},   {'G', 88},   
    {'H', 88},   {'I', 88},   {'J', 88},   {'K', 88},   
    {'L', 88},   {'M', 88},   {'N', 88},   {'O', 88},   
    {'P', 88},   {'Q', 88},   {'R', 88},   {'S', 88},   
    {'T', 88},   {'U', 88},   {'V', 88},   {'W', 88},   
    {'X', 88},   {'Y', 88},   {'Z', 88},   {'[', 2},    
    {']', 2},    {'^', 2},    {'_', 88},   {'a', 168},  
    {'b', 104},  {'c', 168},  {'d', 152},  {'e', 168},  
    {'f', 168},  {'g', 152},  {'h', 152},  {'i', 168},  
    {'j', 88},   {'k', 88},   {'l', 152},  {'m', 88},   
    {'n', 152},  {'o', 152},  {'p', 168},  {'q', 88},   
    {'r', 168},  {'s', 168},  {'t', 168},  {'u', 168},  
    {'v', 104},  {'w', 104},  {'x', 152},  {'y', 152},  
    {'z', 88},   {'{', 2},    {'|', 2},    {'}', 2},    
    {'~', 2},    {'Ё', 88},  {'А', 88},  {'Б', 88},  
    {'В', 88},  {'Г', 88},  {'Д', 88},  {'Е', 88},  
    {'Ж', 88},  {'З', 88},  {'И', 88},  {'Й', 88},  
    {'К', 88},  {'Л', 88},  {'М', 88},  {'Н', 88},  
    {'О', 88},  {'П', 88},  {'Р', 88},  {'С', 88},  
    {'Т', 88},  {'У', 88},  {'Ф', 88},  {'Х', 88},  
    {'Ц', 88},  {'Ч', 88},  {'Ш', 88},  {'Щ', 88},  
    {'Ъ', 88},  {'Ы', 88},  {'Ь', 88},  {'Э', 88},  
    {'Ю', 88},  {'Я', 88},  {'а', 88},  {'б', 88},  
    {'в', 88},  {'г', 88},  {'д', 88},  {'е', 88},  
    {'ж', 88},  {'з', 88},  {'и', 88},  {'й', 88},  
    {'к', 88},  {'л', 88},  {'м', 88},  {'н', 88},  
    {'о', 88},  {'п', 88},  {'р', 88},  {'с', 88},  
    {'т', 88},  {'у', 88},  {'ф', 88},  {'х', 88},  
    {'ц', 88},  {'ч', 88},  {'ш', 88},  {'щ', 88},  
    {'ъ', 88},  {'ы', 88},  {'ь', 88},  {'э', 88},  
    {'ю', 88},  {'я', 88},  {'ё', 88}
};


uint64_t get_categories_set(char32_t c){
    auto it = categories_table.find(c);
    if(it != categories_table.end()){
        return it->second;
    }else{
        return 1ULL << Other;
    }
}
bool Lexer::start_proc(){
    bool t = true;
    state = -1;
    /* For an automaton that processes a token, the state with the number (-1) is
     * the state in which this automaton is initialized. */
    if(belongs(SPACES, char_categories)){
        loc->current_line += U'\n' == ch;
        return t;
    }
    lexem_begin_line = loc->current_line;
    if(belongs(DELIMITER_BEGIN, char_categories)){
        (loc->pcurrent_char)--; automaton = A_delimiter;
        state = -1;
        return t;
    }

    if(belongs(STRING_BEGIN, char_categories)){
        (loc->pcurrent_char)--; automaton = A_string;
        state = 0;
        buffer.clean();
        return t;
    }

    if(belongs(IDKEYWORD_BEGIN, char_categories)){
        (loc->pcurrent_char)--; automaton = A_idKeyword;
        state = 0;
        return t;
    }

    automaton = A_unknown;
    return t;
}

bool Lexer::unknown_proc(){
    return belongs(Other, char_categories);
}

struct Keyword_list_elem{
    std::u32string keyword;
    lexem_code kw_code;
};

static const Keyword_list_elem kwlist[] = {
    {U"array", Array},       {U"bool", Kw_bool},     
    {U"char", Kw_char},      {U"const", Const},      
    {U"continue", Continue}, {U"elif", Elif},        
    {U"else", Else},         {U"endif", Endif},      
    {U"exit", Exit},         {U"false", False},      
    {U"float", Kw_float},    {U"for", For},          
    {U"func", Func},         {U"if", If},            
    {U"in", In},             {U"int", Kw_int},       
    {U"print", Print},       {U"proto", Proto},      
    {U"read", Read},         {U"repeat", Repeat},    
    {U"return", Return},     {U"string", Kw_string}, 
    {U"true", True},         {U"until", Until},      
    {U"var", Var},           {U"void", Kw_void},     
    {U"while", While}
};

#define NUM_OF_KEYWORDS 27

#define THERE_IS_NO_KEYWORD (-1)

static int search_keyword(const std::u32string& finded_keyword){
    int result      = THERE_IS_NO_KEYWORD;
    int low_bound   = 0;
    int upper_bound = NUM_OF_KEYWORDS - 1;
    int middle;
    while(low_bound <= upper_bound){
        middle             = (low_bound + upper_bound) / 2;
        auto& curr_kw      = kwlist[middle].keyword;
        int compare_result = finded_keyword.compare(curr_kw);
        if(0 == compare_result){
            return middle;
        }
        if(compare_result < 0){
            upper_bound = middle - 1;
        }else{
            low_bound   = middle + 1;
        }
    }
    return result;
}

static const std::set<size_t> final_states_for_idkeywords = {
    1
};

bool Lexer::idkeyword_proc(){
    bool t             = true;
    bool there_is_jump = false;
    switch(state){
        case 0:
            if(belongs(IDKEYWORD0, char_categories)){
                state = 1;
                there_is_jump = true;
            }
             else if(belongs(IDKEYWORD1, char_categories)){
                buffer += ch;
                state = 1;
                there_is_jump = true;
            }

            break;
        case 1:
            if(belongs(IDKEYWORD2, char_categories)){
                state = 1;
                there_is_jump = true;
            }
             else if(belongs(IDKEYWORD3, char_categories)){
                buffer += ch;
                state = 1;
                there_is_jump = true;
            }

            break;
        default:
            ;
    }

    if(!there_is_jump){
        t = false;
        if(!is_elem(state, final_states_for_idkeywords)){
            printf("At line %zu unexpectedly ended identifier or keyword.", loc->current_line);
            en->increment_number_of_errors();
        }
        
        int search_result = search_keyword(buffer);
        if(search_result != THERE_IS_NO_KEYWORD) {
            token.code = kwlist[search_result].kw_code;
        }
    }

    return t;
}

static const State_for_char init_table_for_delimiters[] ={
    {15, U'!'}, {40, U'#'}, {8, U'%'},  {25, U'&'}, {38, U'('}, 
    {39, U')'}, {3, U'*'},  {1, U'+'},  {43, U','}, {2, U'-'},  
    {6, U'/'},  {33, U':'}, {42, U';'}, {9, U'<'},  {0, U'='},  
    {12, U'>'}, {41, U'?'}, {44, U'['}, {45, U']'}, {27, U'^'}, 
    {36, U'{'}, {23, U'|'}, {37, U'}'}, {29, U'~'}
};

struct Elem {
    /** A pointer to a string of characters that can be crossed. */
    char32_t*       symbols;
    /** A lexeme code. */
    lexem_code code;
    /** If the current character matches symbols[0], then the transition to the state
     *  first_state;
     *  if the current character matches symbols[1], then the transition to the state
     *  first_state + 1;
     *  if the current character matches symbols[2], then the transition to the state
     *  first_state + 2, and so on. */
    uint16_t        first_state;
};

static const Elem delim_jump_table[] = {
    {const_cast<char32_t*>(U""), Equal, 0},               
    {const_cast<char32_t*>(U""), Plus, 0},                
    {const_cast<char32_t*>(U""), Minus, 0},               
    {const_cast<char32_t*>(U"*"), Mul, 4},                
    {const_cast<char32_t*>(U"."), Pow, 5},                
    {const_cast<char32_t*>(U""), FPow, 0},                
    {const_cast<char32_t*>(U"."), Div, 7},                
    {const_cast<char32_t*>(U""), FDiv, 0},                
    {const_cast<char32_t*>(U""), Mod, 0},                 
    {const_cast<char32_t*>(U"=<"), LT, 10},               
    {const_cast<char32_t*>(U""), LEQ, 0},                 
    {const_cast<char32_t*>(U""), LShift, 0},              
    {const_cast<char32_t*>(U"=>"), GT, 13},               
    {const_cast<char32_t*>(U""), GEQ, 0},                 
    {const_cast<char32_t*>(U""), RShift, 0},              
    {const_cast<char32_t*>(U"=|&^"), LNot, 16},           
    {const_cast<char32_t*>(U""), Nequal, 0},              
    {const_cast<char32_t*>(U"|"), Unknown, 18},           
    {const_cast<char32_t*>(U"&"), Unknown, 19},           
    {const_cast<char32_t*>(U"^"), Unknown, 20},           
    {const_cast<char32_t*>(U""), LNor, 0},                
    {const_cast<char32_t*>(U""), clos, 0},                
    {const_cast<char32_t*>(U""), LNXor, 0},               
    {const_cast<char32_t*>(U"|"), Bor, 24},               
    {const_cast<char32_t*>(U""), Lor, 0},                 
    {const_cast<char32_t*>(U"&"), BAnd, 26},              
    {const_cast<char32_t*>(U""), LAnd, 0},                
    {const_cast<char32_t*>(U"^"), BXor, 28},              
    {const_cast<char32_t*>(U""), LXor, 0},                
    {const_cast<char32_t*>(U"^|&"), BNot, 30},            
    {const_cast<char32_t*>(U""), BNXor, 0},               
    {const_cast<char32_t*>(U""), BNor, 0},                
    {const_cast<char32_t*>(U""), BNAnd, 0},               
    {const_cast<char32_t*>(U"=:"), Colon, 34},            
    {const_cast<char32_t*>(U""), Assign, 0},              
    {const_cast<char32_t*>(U""), after_label, 0},         
    {const_cast<char32_t*>(U""), Open_body_func, 0},      
    {const_cast<char32_t*>(U""), close_body_func, 0},     
    {const_cast<char32_t*>(U""), Open_list_of_names, 0},  
    {const_cast<char32_t*>(U""), Close_list_of_names, 0}, 
    {const_cast<char32_t*>(U""), Dim_size, 0},            
    {const_cast<char32_t*>(U""), cond_op, 0},             
    {const_cast<char32_t*>(U""), Semicolon, 0},           
    {const_cast<char32_t*>(U""), Comma, 0},               
    {const_cast<char32_t*>(U""), Open_list_of_expr, 0},   
    {const_cast<char32_t*>(U""), Close_list_of_expr, 0}
};

bool Lexer::delimiter_proc(){
    bool t = false;
    if(-1 == state){
        state = get_init_state(ch, init_table_for_delimiters,
                               sizeof(init_table_for_delimiters)/sizeof(State_for_char));
        token.code = delim_jump_table[state].code;
        t = true;
        return t;
    }
    Elem elem = delim_jump_table[state];
    token.code = delim_jump_table[state].code;
    int y = search_char(ch, elem.symbols);
    if(y != THERE_IS_NO_CHAR){
        state = elem.first_state + y; t = true;
    }
    return t;
}

static const std::set<size_t> final_states_for_strings = {
    1
};

bool Lexer::string_proc(){
    bool t             = true;
    bool there_is_jump = false;
    switch(state){
        case 0:
            if(belongs(STRING_BEGIN, char_categories)){
                state = 2;
                there_is_jump = true;
            }

            break;
        case 1:
            if(belongs(STRING_BEGIN, char_categories)){
                buffer += ch;
                state = 2;
                there_is_jump = true;
            }

            break;
        case 2:
            if(ch != U'\"'){
                buffer += ch;
                state = 2;
                there_is_jump = true;
            }
             else if(belongs(STRING_BEGIN, char_categories)){
                state = 1;
                there_is_jump = true;
            }

            break;
        default:
            ;
    }

    if(!there_is_jump){
        t = false;
        if(!is_elem(state, final_states_for_strings)){
            printf("At line %zu unexpectedly ended a string literal.", loc->current_line);
            en->increment_number_of_errors();
        }
        token.code=(buffer.length()==1)?Char:String;
            token.string_index = strs -> insert(buffer);
    }

    return t;
}

void Lexer::none_proc(){
    /* This subroutine will be called if, after reading the input text, it turned
     * out to be in the A_start automaton. Then you do not need to do anything. */
}

void Lexer::unknown_final_proc(){
    /* This subroutine will be called if, after reading the input text, it turned
     * out to be in the A_unknown automaton. Then you do not need to do anything. */
}

void Lexer::idkeyword_final_proc(){
    if(!is_elem(state, final_states_for_idkeywords)){
        printf("At line %zu unexpectedly ended identifier or keyword.", loc->current_line);
        en->increment_number_of_errors();
    }

    int search_result = search_keyword(buffer);
    if(search_result != THERE_IS_NO_KEYWORD) {
        token.code = kwlist[search_result].kw_code;
    }

}

void Lexer::delimiter_final_proc(){
        
    token.code = delim_jump_table[state].code;
    
}

void Lexer::string_final_proc(){
    if(!is_elem(state, final_states_for_strings)){
        printf("At line %zu unexpectedly ended a string literal.", loc->current_line);
        en->increment_number_of_errors();
    }
    token.code=(buffer.length()==1)?Char:String;
    token.string_index = strs -> insert(buffer);
}

Lexem_info Lexer::current_lexem(){
    automaton = A_start; token.code = None;
    lexem_begin = loc->pcurrent_char;
    bool t = true;
    while((ch = *(loc->pcurrent_char)++)){
        char_categories = get_categories_set(ch); //categories_table[ch];
        t = (this->*procs[automaton])();
        if(!t){
            /* We get here only if the lexeme has already been read. At the same time,
             * the current automaton reads the character immediately after the end of
             * the token read, based on this symbol, it is decided that the token has
             * been read and the transition to the next character has been made.
             * Therefore, in order to not miss the first character of the next lexeme,
             * we need to decrease the pcurrent_char pointer by one. */
            (loc->pcurrent_char)--;
            return token;
        }
    }
    /* Here we can be, only if we have already read all the processed text. In this
     * case, the pointer to the current symbol indicates a byte, which is immediately
     * after the zero character, which is a sign of the end of the text. To avoid
     * entering subsequent calls outside the text, we need to go back to the null
     * character. */
    (loc->pcurrent_char)--;
    /* Further, since we are here, the end of the current token (perhaps unexpected)
     * has not yet been processed. It is necessary to perform this processing, and,
     * probably, to display any diagnostics. */
    (this->*finals[automaton])();
    return token;
}


