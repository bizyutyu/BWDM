#ifndef _MAKE_DECISION_TABLE
#define _MAKE_DECISION_TABLE

#include<stdio.h>
#include<stdlib.h>
#include<string.h>
#include <regex.h>
#include<math.h>
#include "header_for_lexeme_id.h"

#define BUFSIZE 1024
#define NULLCHAR '\0'

//#define PATH_APPFILE "../data/FizzBuzz.vdmpp.app"
//#define PATH_CSVFILE "../data/FizzBuzz.csv"

//#define PATH_APPFILE "../data/MyersTriangle.vdmpp.app"
//#define PATH_CSVFILE "../data/MyersTriangle.csv"

#define PATH_DATA_DIRECTORY "../data/"

//#define PATH_APPFILE "../data/Best_course.vdmpp.app"
//#define PATH_CSVFILE "../data/Best_course.csv"


#define EXTENSION_OF_INPUTFILE ".vdmpp"
#define EXTENSION_OF_APP ".vdmpp.app"
#define EXTENSION_OF_OUTPUTFILE ".csv"

enum Function_result {Result_true,Result_false};
enum Access_modifier {private,protected,public};
enum Bool_value {no_value,value_true, value_false};
enum Definition_type {function,operation};
enum Variable_type {void_type,char_type,int_type,bool_type,unknown_type};
enum Condition_type {no_type,undefined,pre_condition,post_condition,normal_condition};


//実行経路データ
enum Node_type{not_yet_decided,branch_node,action};
typedef struct branch_tree_node{
	enum Node_type type;
	int condition_id;
	int action_id;
	struct branch_tree_node *next;
	struct branch_tree_node *true_branch;
	struct branch_tree_node *false_branch;
}branch_tree_node;

//内部データを見る為の関数群
//look_internal_data.c
void look_class_list();
void look_lexeme_list();
void look_action_list();


//filename_control.c
//入力ファイル、出力ファイルの管理
void extract_filename(char *input_filename);
void get_input_filename(char *filename_buf);
void get_output_filename(char *filename_buf);

//実行時、ツーザが指定したコマンドを管理
//command_line_argument.c
void extract_command_line_argument(int argc,char **argv);
enum Function_result option_action_value_empty_in_function();
enum Function_result option_not_output_return_bool_value_in_function();
enum Function_result option_not_use_logic_operation();
enum Function_result option_run_fast();

//vdmpp.appファイルからトークンとトークンIDを抜き出す
//lexeme_list.c
void make_lexeme_list();
void lexeme_list_index_init();
void go_next_lexeme_node();
enum Function_result can_go_next_lexeme_node();
int get_lexeme_id_from_lexeme_node();
void get_parser_command(char *buf);
void get_lexeme_str_from_lexeme_node(char *target_buf);
char *get_lexeme_str_without_escape_string();


//--------------------ディレクトリ"class_definition"------------------
//トークンとトークンIDを、クラスごとまたはクラス定義ごとに分ける
//クラス定義識別部と抽象構文木に対するインデックスの機能を持つ
//class_definition.c
void extract_class_definition();

void class_list_index_init();
void go_next_class_node();
enum Function_result can_go_next_class_node();
void get_class_name_from_class_node(char *class_name_buf);

//関数定義についての情報を取得
//function_definition.c
void lexeme_list_in_function_index_init();
void go_next_function_node();
enum Access_modifier get_access_modifier_from_function_node();
enum Function_result is_this_function_static();
void go_next_lexeme_node_in_function();
enum Function_result is_this_class_have_function();
enum Function_result can_go_next_function_node();
enum Function_result can_go_next_lexeme_node_in_function();
void get_function_name_from_function_node(char *function_name_buf);
void get_str_from_lexeme_node_in_function(char *str_buf);
int get_lexeme_id_from_lexeme_node_in_function();
enum Variable_type get_return_value_type_from_function_node();

//操作定義についての情報を取得
//operation_definition.c
void lexeme_list_in_operation_index_init();
void go_next_operation_node();
enum Access_modifier get_access_modifier_from_operation_node();
enum Function_result is_this_operation_static();
void go_next_lexeme_node_in_operation();
enum Function_result is_this_class_have_operation();
enum Function_result can_go_next_operation_node();
enum Function_result can_go_next_lexeme_node_in_operation();
void get_operation_name_from_operation_node(char *operation_name_buf);
void get_str_from_lexeme_node_in_operation(char *str_buf);
int get_lexeme_id_from_lexeme_node_in_operation();
enum Variable_type get_return_value_type_from_operation_node();


//--------------ディレクトリcondition_list------------------
//このディレクトリは条件管理部にあたる

//条件データを管理
//condition_list/condition_list.c
void begin_add_a_condition_node(enum Condition_type type);
void add_lexeme_data_for_condition_node(int lexeme_id,char *lexeme_str);
void end_add_a_condition_node();
enum Function_result pre_or_post_condition_is_true();

int get_condition_id_about_under_construction();
int get_condition_number();
enum Function_result condition_is_true(int condition_id);

void look_condition_list();

//単一条件データを管理
//condition_list/condition_branch_tree.c
void search_single_condition_str(int single_condition_id,char buf[BUFSIZE]);
int get_single_condition_number();
void make_new_bool_value_array_for_search_condition_branch_tree();
void set_bool_value_for_search_condition_branch_tree(int row_id);
void free_condition_list();

//---------------ここからデシジョンテーブル生成---------------

//make_all_decition_table.c
//すべてのクラス定義に関するデシジョンテーブルを生成(現在は関数定義のみ)
void make_all_decision_table();


//branch_tree_for_function.c
//関数定義から実行経路データを取得
branch_tree_node *extract_branch_tree_from_function();
//関数のデシジョンテーブル生成
void make_decision_table_for_function(branch_tree_node *root);

//branch_tree.c
//記述部にあたる。実行経路データからデシジョンテーブル(内部データ)を生成
void make_decision_table_for_function(branch_tree_node *root);
//実行経路データの削除
void free_function_branch_tree(branch_tree_node *target);


//order_make_operation_decisiontable.c
//一時的に作ったもの
void order_make_operation_decisiontable();


//action_list.c
//動作データについて管理する
void make_new_action_list();
int add_action_node(char *action_buf);
int get_action_node_number();
void get_action_name(int node_id,char *buf);
void free_action_list();


//decision_table.c
//デシジョンテーブルの内部データを保持
//記述部、出力部は、これらの関数を呼び出すことによってデシジョンテーブルの雛形生成、内容の追加、出力を行う。
void begin_make_decision_table();
void input_class_name_for_decision_table(char *class_name);
void input_definition_type_for_decision_table(enum Definition_type definition_type);
void input_definition_name_for_decision_table(char *definition_name);
void input_condition_num_for_decision_table(int condition_num);
void input_action_num_for_decision_table(int action_num);
void input_condition_name_for_decision_table(char *condition_name);
void input_action_name_for_decision_table(char *action_name);
void input_bool_value_for_action(int line_id,int row_id,enum Bool_value result);
void output_decision_table();

enum Bool_value get_bool_value_from_condition_decision_table(int line_id,int row_id);
int get_row_num();

void look_decision_table();


//一時的
void output_operation_decision_table(char *name);

#endif