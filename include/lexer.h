#ifndef LEXER_H
#define LEXER_H

#include "../include/abstract_scaner.h"
#include "../include/error_count.h"
#include "../include/location.h"
#include <string>"

enum lexem_code : unsigned short {
    None,       Unknown,     sp,         
    bp,         r0,          r1,         
    r2,         r3,          r4,         
    r5,         r6,          r7,         
    r8,         r9,          r10,        
    r11,        r12,         r13,        
    r14,        r15,         r16,        
    r17,        r18,         r19,        
    r20,        r21,         r22,        
    r23,        r24,         r25,        
    r26,        r27,         r28,        
    r29,        r30,         r31,        
    f0,         f1,          f2,         
    f3,         f4,          f5,         
    f6,         f7,          f8,         
    f9,         f10,         f11,        
    f12,        f13,         f14,        
    f15,        f16,         f17,        
    f18,        f19,         f20,        
    f21,        f22,         f23,        
    f24,        f25,         f26,        
    f27,        f28,         f29,        
    f30,        f31,         Equal,      
    Plus,       Minus,       Mul,        
    Div,        Mod,         LT,         
    GT,         LEQ,         GEQ,        
    Nequal,     FDiv,        Lor,        
    LNor,       LNot,        LAnd,       
    LNand,      LXor,        LNXor,      
    Bor,        BNor,        BXor,       
    BNXor,      BAnd,        BNAnd,      
    LShift,     RShift,      BNot,       
    Pow,        FPow,        Assign,     
    Open_func,  close_func,  Open_round, 
    Close_round,cond_op,     after_label,
    Open_square,Close_square,Semicolon,  
    Comma,      Dim_size,    Colon,      
    String,     If,          Float,      
    Else,       Var,         Int,        
    Bool,       Char,        Void,       
    Array,      True,        False,      
    Proto,      Func,        Const,      
    Elif,       Endif,       For,        
    In,         While,       Repeat,     
    Until,      Exit,        Continue,   
    Return,     Read,        Print,      
    Kw_bool,    Kw_string,   Kw_float,   
    Kw_int,     Kw_char,     Kw_void,    
    Single,     Double,      Extended,   
    Quatro,     
};

struct Lexem_info{
    lexem_code code;
    union{
        size_t    ident_index;
unsigned __int128 int_val;__float128 float_val;
    };
};

class Lexer : public Abstract_scaner<Lexem_info> {
public:
    Lexer() = default;
    Lexer(Location* location, const Errors_and_tries& et) :
        Abstract_scaner<Lexem_info>(location, et) {};
    Lexer(const Lexer& orig) = default;
    virtual ~Lexer() = default;
    virtual Lexem_info current_lexem();
private:
    enum Automaton_name{
        A_start,     A_unknown, A_idKeyword, 
        A_delimiter, A_number
    };
    Automaton_name automaton; /* current automaton */

   typedef bool (Lexer::*Automaton_proc)();
    /* This is the type of pointer to the member function that implements the
     * automaton that processes the lexeme. This function must return true if
     * the lexeme is not yet parsed, and false otherwise. */

    typedef void (Lexer::*Final_proc)();
    /* And this is the type of the pointer to the member function that performs
     * the necessary actions in the event of an unexpected end of the lexeme. */

    static Automaton_proc procs[];
    static Final_proc     finals[];

    /* Lexeme processing functions: */
    bool start_proc();     bool unknown_proc();   
    bool idkeyword_proc(); bool delimiter_proc(); 
    bool number_proc();
    /* functions for performing actions in case of an
     * unexpected end of the token */
    void none_proc();            void unknown_final_proc();   
    void idkeyword_final_proc(); void delimiter_final_proc(); 
    void number_final_proc();
};
#endif
