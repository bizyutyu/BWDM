package com.github.korosuke613.bwdm

import java.lang.reflect.Method

class Util {
    companion object {

        fun isNumber(num: String): Boolean {
            return try {
                Integer.parseInt(num)
                true
            } catch (e: NumberFormatException) {
                false
            }

        }

        fun getOperator(condition: String): String {
            return when {
                condition.contains("<=") -> "<="
                condition.contains(">=") -> ">="
                condition.contains("<>") -> "<>"
                condition.contains("<") -> "<"
                condition.contains(">") -> ">"
                condition.contains("mod") -> "mod"
                condition.contains("=") -> "="
                condition.contains("+") -> "+"
                else -> "other"
            }
        }

		fun getComparisonOperator(condition: String): String {
			return when { 
                condition.contains("or") -> "or"
                condition.contains("and") -> "and"
                condition.contains("=>") -> "=>"
                condition.contains("<=") -> "<="
                condition.contains(">=") -> ">="
                condition.contains("<>") -> "<>"
                condition.contains("<") -> "<"
                condition.contains(">") -> ">"
                condition.contains("=") -> "="
                else -> "other"
			}
		}

        @Throws(NoSuchFieldException::class, IllegalAccessException::class)
        fun getPrivateField(_target_obj: Any, _field_name: String): Any {
            val c = _target_obj.javaClass
            val f = c.getDeclaredField(_field_name)
            f.isAccessible = true
            return f.get(_target_obj)
        }


        @Throws(NoSuchMethodException::class)
        fun getPrivateMethod(_target_obj: Any, _method_name: String): Method {
            val c = _target_obj.javaClass
            val m = c.getMethod(_method_name)
            m.isAccessible = true
            return m
        }

        val methodName: String
            get() = Thread.currentThread().stackTrace[2].methodName

        fun printTestResults(_expected: String, _actual: String) {
            println("Exp.:$_expected  Act.:$_actual")
        }
    }


}
