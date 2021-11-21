import os
import re
import math

class Compiler:

    #Constructor
    def __init__(self):
        pass

    #Global Variables
    _multiLineCommentActive = False      #boolean
    _statementsValid = False             #boolean
    _lineNumber = 0                      #int
    _errorCount = 0                      #int
    _caseCount = 0                       #int
    _ifCount = 0                         #int
    _elseCount = 0                       #int
    _varFloatCount = 0                   #int
    _varNumCount = 0                     #int
    _varStringCount = 0                  #int
    _switchCount = 0                     #int
    _forLoopCount = 0                    #int
    _stringOperationCount = 0            #int
    _forToCount = 0
    _forStepCount = 0
    _stringConcatCount = 0
    _arrayCount = 0
    _currentSwitch = []
    _currentForLoop = []
    _currentIf = []
    _forLoopParametersStack = []        
    _errorMessages = []                  #List of Key Value pairs [[],[]]
    _uninitializedValues = []            #List of Key Value pairs [[],[]]
    _initializedValues = []              #List of Key Value pairs [[],[]]
    _operations = []
    _operatorCount = 0
    _programVariableName = ''            #string
    _procedures = []
    _procedureParameters = []
    _assemblyProcedureCount = 0
    _tempVariables = []
    _openCurlyBrace = [] #This will store what curly braces are open
    _switchVariable = []
    _negativeNumberIndexes = []
    _variableValues = []
    _variablesUsed = []
    _writeOperationVariables = []
    _writeOperationVariableDependencies = []

    _switchNeedsCurlyBrace = False #These will indicate which curly brace it is. So when we run into a curly brace we will call a method that fills in the openCurlyBrace with the specific curly brace scope that is open
    _caseNeedsCurlyBrace = False
    _defaultCaseNeedsCurlyBrace = False
    _ifNeedsCurlyBrace = False
    _elseNeedsCurlyBrace = False
    _forLoopNeedsCurlyBrace = False
    _procedureNeedsCurlyBrace = False
    _constantFolding = False
    _constantPropagation = False
    _deadCodeElimination = False
    _multiplyOrDivideBy2 = False
    _uselessCodeRemoval = False

    def AddOrUpdateVariableValue(self, variableName, value):
        
        for variable in self._variableValues:
            if variable[0] == variableName:
                variable[1] = value
                return
        
        self._variableValues.append([variableName, value])
    
    def GetVariableValue(self, variableName):

        for variable in self._variableValues:
            if variable[0] == variableName:
                return variable[1]
        return None

    def AssemblyCodeForNumOrVar(self, value, assemblyFile):
        if self.IsNumber(value) or self.IsNegativeNumber(value):
            assemblyFile.write(value + '\n')
        else:
            assemblyFile.write('DWORD[' + value + ']\n')

    def CloseCurlyBrace(self):

        closingSection = self._openCurlyBrace[len(self._openCurlyBrace) - 1]

        if closingSection[0] == 'switch':
            self._operations.append(['endSwitch', closingSection[1]])
            self._currentSwitch.pop()

        elif closingSection[0] == 'case':
            self._operations.append(['endCase', closingSection[1], self._currentSwitch[len(self._currentSwitch) - 1]])
            # assemblyFile.write('\tjmp\t_end_switch_' + str(operation[2]) + '\n')

        elif closingSection[0] == 'defaultCase':
            pass

        elif closingSection[0] == 'if':
            self._operations.append(['endIfStatement', closingSection[1]])
            self._currentIf.pop()
        
        elif closingSection[0] == 'else':
            self._operations.append(['endElse', closingSection[1]])
            self._elseCount += 1

        elif closingSection[0] == 'for':
            parameters = self._forLoopParametersStack[len(self._forLoopParametersStack) - 1]
            self._operations.append(['endForLoop', parameters[0], parameters[1], parameters[3]])
            self._forLoopParametersStack.pop()
            self._currentForLoop.pop()

        elif closingSection[0] == 'procedure' or closingSection == 'procedure':
            self._operations.append('endProcedure')
            self.RefreshProcedureParameters(self._procedures[(len(self._procedures) - 1)])

        self._openCurlyBrace.pop()

    #Compiler Main (Start of compiler)
    def CompilerMain(self):

        fileName = input('Enter the file name you wish to compile: ')

        # Optimizations
        response = input('\nWould you like use Constant Folding? [Y] or [N]: ')
        if response == 'Y' or response == 'y':
            self._constantFolding = True

        response = input('\nWould you like use Constant Propagation? [Y] or [N]: ')
        if response == 'Y' or response == 'y':
            self._constantPropagation = True

        response = input('\nWould you like perform Dead Code Elimination? [Y] or [N]: ')
        if response == 'Y' or response == 'y':
            self._deadCodeElimination = True

        response = input('\nWould you like to use the multiply or divide by 2 peep hole optimization? [Y] or [N]: ')
        if response == 'Y' or response == 'y':
            self._multiplyOrDivideBy2 = True
        
        response = input('\nWould you like use the useless code removal peep hole optimization? [Y] or [N]: ')
        if response == 'Y' or response == 'y':
            self._uselessCodeRemoval = True

        if os.path.isfile(fileName):
            programFile = open(fileName, 'r')
            result = self.ProcessProgramFile(programFile, fileName)
            programFile.close()
                
            if result[0][1] == 'valid': #[[0, 'valid']]

                if self._deadCodeElimination:
                    self.DeadCodeElimination()
                assemblyFile = self.CreateAssembly(fileName)
                self.GenerateAssemblyFile(assemblyFile)
                assemblyFile.close()
            
            errorFile = self.CreateErrorFile(fileName)
            self.GenerateErrorFile(errorFile, result)
            errorFile.close()
                
        else:
            pass
            #Error. No such file exists
    
    def ConstantFolding(self, expression):
        # This method takes the prefixExpression and simplifies it if it is not a single number or variable assignment
        
        processComplete = False
        openParenthesis = False

        if self._operatorCount == 0:
            return expression

        while not processComplete:

            index = 0
            tempOperatorIndex = 0
            tempOperator = ''
            tempOperand1Index = -1
            tempOperand2Index = -1
            tempOperand1 = ''
            tempOperand2 = ''
            tempVariable = ''
            stringTempResult = ''
            tempOperators = []

            for char in expression:
                
                if char == ' ':
                    index += 1
                    continue
                else:
                    if self.IsOperator(char) or tempVariable == '':
                        if tempOperand1Index == -1 and (not self.IsOperator(char) or self.IsNegativeNumberIndex(index)):
                            tempOperand1Index = index
                        elif tempOperand2Index == -1 and (not self.IsOperator(char) or self.IsNegativeNumberIndex(index)):
                            tempOperand2Index = index
                        tempVariable = char
                    else:
                        tempVariable = tempVariable + char

                if expression[index + 1] == ' ' and not self.IsOperator(tempVariable):
                    if self.IsNumber(tempVariable) or self.VariableHasValue(tempVariable) or self.IsNegativeNumber(tempVariable) or self.IsFloatingPointNumber(tempVariable) or self.IsNegativeFloatingPointNumber(tempVariable):
                        if tempOperand1 == '':
                            if self.VariableHasValue(tempVariable):
                                tempOperand1 = self.GetVariableName(tempVariable)
                            else:
                                tempOperand1 = tempVariable
                            tempVariable = ''
                        elif index - 1 != tempOperatorIndex:
                            tempOperand2Index = index
                            if self.VariableHasValue(tempVariable):
                                tempOperand2 = self.GetVariableName(tempVariable)
                            else:
                                tempOperand2 = tempVariable
                elif self.IsOperator(tempVariable) and not self.IsNegativeNumberIndex(index) and not openParenthesis:
                    tempOperators.append([tempVariable, index])
                    tempOperatorIndex = index
                    tempOperator = tempVariable
                    tempVariable = ''
                    tempOperand1 = ''
                    tempOperand1Index = -1
                
                if tempOperand2 != '':

                    if self.VariableNameExists(tempOperand1):
                        tempOperand1 = tempOperand2
                        tempOperand2 = ''
                        tempVariable = ''
                        tempOperand1Index = tempOperand2Index
                        tempOperand2Index = 0
                        previousOperator = tempOperators[len(tempOperators) - 2][0]
                        if tempOperator == previousOperator or (previousOperator == '+' and tempOperator == '-') or (previousOperator == '-' and tempOperator == '+'):
                            tempOperator = previousOperator
                            tempOperatorIndex = tempOperators[len(tempOperators) - 2][1]
                        else:
                            tempOperator = ''
                            tempOperatorIndex = 0
                            tempOperand1 = ''
                            tempOperand1Index = -1


                    elif self.VariableNameExists(tempOperand2):
                        tempOperand2 = ''
                        tempVariable = ''
                        tempOperand2Index = -1
                        previousOperator = tempOperators[len(tempOperators) - 2][0]
                        if tempOperator == previousOperator or (previousOperator == '+' and tempOperator == '-') or (previousOperator == '-' and tempOperator == '+'):
                            tempOperator = previousOperator
                            tempOperatorIndex = tempOperators[len(tempOperators) - 2][1]
                        else:
                            tempOperator = ''
                            tempOperatorIndex = 0
                            tempOperand1 = ''
                            tempOperand1Index = -1
                    else:
                        num1 = 0
                        num2 = 0
                        float1 = 0.0
                        float2 = 0.0
                        isFloat = False

                        if self.IsNumber(tempOperand1):
                            num1 = int(tempOperand1)
                        elif self.IsNegativeNumber(tempOperand1):
                            num1 = 0 - int(tempOperand1[1:len(tempOperand1)])
                        elif self.IsFloatingPointNumber(tempOperand1):
                            float1 = float(tempOperand1)
                            isFloat = True
                        elif self.IsNegativeFloatingPointNumber(tempOperand1):
                            float1 = 0.0 - float(tempOperand1[1:len(tempOperand1)])
                            isFloat = True
                        
                        if self.IsNumber(tempOperand2):
                            num2 = int(tempOperand2)
                        elif self.IsNegativeNumber(tempOperand2):
                            num2 = 0 - int(tempOperand2[1:len(tempOperand2)])
                        elif self.IsFloatingPointNumber(tempOperand2):
                            float2 = float(tempOperand2)
                            isFloat = True
                        elif self.IsNegativeFloatingPointNumber(tempOperand2):
                            float2 = 0.0 - float(tempOperand2[1:len(tempOperand2)])
                            isFloat = True

                        if tempOperator == '+':
                            if not isFloat:
                                stringTempResult = str(num1 + num2)
                            else:
                                stringTempResult = str(float1 + float2)
                        elif tempOperator == '-':
                            if not isFloat:
                                stringTempResult = str(num1 - num2)
                            else:
                                stringTempResult = str(float1 - float2)
                        elif tempOperator == '*':
                            if not isFloat:
                                stringTempResult = str(num1 * num2)
                            else:
                                stringTempResult = str(float1 * float2)
                        elif tempOperator == '^':
                            if not isFloat:
                                stringTempResult = str(num1 ^ num2)
                            else:
                                stringTempResult = str(float1 ^ float2)

                        self._operatorCount -= 1
                        if tempOperatorIndex == 0:
                            expression = expression[tempOperatorIndex + 1: len(expression)]
                        else:
                            expression = expression[0:tempOperatorIndex] + expression[tempOperatorIndex + 1: len(expression)]

                        if tempOperand1Index == 0 or tempOperand1Index - 1 == 0:
                            expression = stringTempResult + expression[tempOperand2Index: len(expression)]
                            break
                        else:
                            expression = expression[0:tempOperand1Index - len(tempOperand1)] + stringTempResult + expression[tempOperand2Index: len(expression)]
                            if self.IsNegativeNumber(stringTempResult):
                                self._negativeNumberIndexes.append(tempOperand1Index - len(tempOperand1))
                            if expression[0] == ' ':
                                expression = expression[1: len(expression)]
                            break
                    
                    index += 1
                else:
                    index += 1

            if tempOperand2 == '':
                processComplete = True

        return expression

    def ConstantPropagation(self, expression):
        
        processComplete = False

        while not processComplete:

            index = 0
            tempVariableIndex = -1
            tempVariable = ''

            for char in expression:
                
                if index == len(expression) - 1:
                    processComplete = True

                if char == ' ':
                    index += 1
                    continue
                else:
                    if tempVariable == '':
                        if tempVariableIndex == -1 and not self.IsOperator(char):
                            tempVariableIndex = index
                        tempVariable = char
                    else:
                        tempVariable = tempVariable + char

                if expression[index + 1] == ' ':
                    if self.VariableHasValue(tempVariable):
                        value = self.GetVariableValue(self.GetVariableName(tempVariable))
                        if self.IsNumber(value) or self.IsFloatingPointNumber(value):
                            expression = expression[0:tempVariableIndex] + value + expression[index + 1:len(expression)]
                            break
                        elif self.IsNegativeNumber(value) or self.IsNegativeFloatingPointNumber(value):
                            self._negativeNumberIndexes.append(tempVariableIndex)
                            expression = expression[0:tempVariableIndex] + value + expression[index + 1:len(expression)]
                            break
                    else:
                        tempVariable = ''
                        tempVariableIndex = -1

                elif self.IsOperator(tempVariable) and not self.IsNegativeNumberIndex(index):
                    tempVariable = ''
                    tempVariableIndex = -1
                
                index += 1

        return expression

    def CreateAssembly(self, fileName):
        assemblyFileName = fileName[0:fileName.index(".")] + '.asm'
        return open(assemblyFileName, "w")
    
    def CreateErrorFile(self, fileName):
        errorFileName = fileName[0:fileName.index(".")] + '.err'
        return open(errorFileName, "w")

    def DeadCodeElimination(self):
        
        length = len(self._operations)

        for i in reversed(range(length)):
            if self._operations[i][0] == 'write':
                if self.VariableHasValue(self._operations[i][1]):
                    self._writeOperationVariableDependencies.append(self._operations[i][1])

                    if not self._operations[i][1] in self._variablesUsed:
                        self._variablesUsed.append(self._operations[i][1])

            elif self._operations[i][0] == 'stringVariableAssignment' or self._operations[i][0] == 'floatVariableAssignment' or self._operations[i][0] == 'numVariableAssignment':
                # self._operations.append(['numVariableAssignment', result, '', variable])
                # self._operations.append(['floatVariableAssignment', result, '', self.GetVariableName(variableName)])
                # self._operations.append(['stringVariableAssignment', tempOperand1, '', variable])
                if self.VariableIsADependencyToWriteStatment(self._operations[i][3]):

                    self._writeOperationVariableDependencies.remove(self._operations[i][3])

                    if not self.IsNumber(self._operations[i][1]) and not self.IsNegativeNumber(self._operations[i][1]) and not self.IsFloatingPointNumber(self._operations[i][1]) and not self.IsNegativeFloatingPointNumber(self._operations[i][1]):
                        self._writeOperationVariableDependencies.append(self._operations[i][1])
                        
                        if not self._operations[i][1] in self._variablesUsed:
                            self._variablesUsed.append(self._operations[i][1])
                else:
                    del self._operations[i]
                    
            elif (self._operations[i][0] == 'add' or self._operations[i][0] == 'addFloat' or self._operations[i][0] == 'subtract' or self._operations[i][0] == 'subtractFloat' or self._operations[i][0] == 'multiply' or self._operations[i][0] == 'multiplyFloat' or self._operations[i][0] == 'exponentiate' or self._operations[i][0] == 'stringConcatenationAssignment'):
                
                if self.VariableIsADependencyToWriteStatment(self._operations[i][3]):

                    self._writeOperationVariableDependencies.remove(self._operations[i][3])

                    if not self.IsNumber(self._operations[i][1]) and not self.IsNegativeNumber(self._operations[i][1]) and not self.IsFloatingPointNumber(self._operations[i][1]) and not self.IsNegativeFloatingPointNumber(self._operations[i][1]):
                        self._writeOperationVariableDependencies.append(self._operations[i][1])
                        
                        if not self._operations[i][1] in self._variablesUsed:
                            self._variablesUsed.append(self._operations[i][1])

                    if not self.IsNumber(self._operations[i][2]) and not self.IsNegativeNumber(self._operations[i][2]) and not self.IsFloatingPointNumber(self._operations[i][2]) and not self.IsNegativeFloatingPointNumber(self._operations[i][2]):
                        self._writeOperationVariableDependencies.append(self._operations[i][2])
                        
                        if not self._operations[i][2] in self._variablesUsed:
                            self._variablesUsed.append(self._operations[i][2])
                else:
                    del self._operations[i]

                # operation[3] == 'result' if this is found in a later write statement then we are dependent upon these variables in 1 and 2
                # self._operations.append(['stringConcatenationAssignment', tempOperand1, tempOperand2, variable])




            # Maybe not need to do this.
            # elif self._operations[i][0] == 'writeItemFromArray':
            #     # self._operations.append(['writeItemFromArray', array[4], 4, array[1]])
            #     writeOperationVariables.append(self._operations[i][3])

            #Array stuff. We'll wait until later for this
            # elif operation[0] == 'arrayOffset':
            #     # self._operations.append(['arrayOffset', delta[j], arrayList[j]])
            #     tempRegister = 'esi'
            #     if register == 'esi':
            #         tempRegister = 'edx'
            #     elif register == 'edx':
            #         tempRegister = 'ecx'

            #     assemblyFile.write('\tmov\t' + tempRegister + ',\t' + str(operation[1]) + '\n')
            #     assemblyFile.write('\timul\t' + tempRegister + ',\t' + str(operation[2]) + '\n')
            #     assemblyFile.write('\tadd\t' + register + ',\t' + tempRegister + '\n')
            
            # elif operation[0] == 'arrayOffsetVariable':
            #     # self._operations.append(['arrayOffsetVariable', delta[j], arrayList[j]])
            #     tempRegister = 'esi'
            #     if register == 'esi':
            #         tempRegister = 'edx'
            #     elif register == 'edx':
            #         tempRegister = 'ecx'

            #     assemblyFile.write('\tmov\t' + tempRegister + ',\t' + str(operation[1]) + '\n')
            #     assemblyFile.write('\timul\t' + tempRegister + ',\tDWORD[' + str(operation[2]) + ']\n')
            #     assemblyFile.write('\tadd\t' + register + ',\t' + tempRegister + '\n')

            # Might need to check this out too
            # elif operation[0] == 'allocateToArray':
            #     # self._operations.append(['allocateToArray', array[4], 4, array[1], result])
            #     assemblyFile.write('\tsub\t' + register + ',\t' + str(operation[1]) + '\n')
            #     assemblyFile.write('\timul\t' + register + ',\t' + str(operation[2]) + '\n')
            #     assemblyFile.write('\tadd\t' + register + ',\t' + operation[3] + '\n')
            #     assemblyFile.write('\tmov\tDWORD[' + register + '],\t' + operation[4] + '\n')
            
            # Might need to check this out
            # elif operation[0] == 'allocateValueFromVariableToArray':
            #     # valueToAdd = ['num_array', arrayVariableName, arraySize, delta, lowerBound]
            #     # self._operations.append(['allocateToArray', array[4], 4, array[1], result])
            #     tempRegister = 'esi'
            #     if register == 'esi':
            #         tempRegister = 'edx'
            #     elif register == 'edx':
            #         tempRegister = 'ecx'
            #     assemblyFile.write('\tsub\t' + register + ',\t' + str(operation[1]) + '\n')
            #     assemblyFile.write('\timul\t' + register + ',\t' + str(operation[2]) + '\n')
            #     assemblyFile.write('\tadd\t' + register + ',\t' + operation[3] + '\n')
            #     assemblyFile.write('\tmov\t' + tempRegister + ',\tDWORD[' + operation[4] + ']\n')
            #     assemblyFile.write('\tmov\tDWORD[' + register + '],\t' + tempRegister + '\n')

    def FindPrefixExpression(self, expression):

        tempToken = ''
        prefixExpression = ''
        previousOperator = ''
        token = ''
        openParenthesesCount = 0
        parenExpression = ''
        parenPrefixExpression = ''
        
        for i in range(0, len(expression)):
            
            if expression[i] == ' ':
                continue

            if expression[i] == ';':
                if openParenthesesCount > 0: #Error: No closing parentheses
                    self._errorCount += 1
                    errorMessage = 'Syntax error on line ' + str(self._lineNumber) + '. Missing closing parentheses ")".'
                    self._errorMessages.append([self._lineNumber, errorMessage])
                
                elif openParenthesesCount < 0: #Error: No opening parentheses in statement
                    self._errorCount += 1
                    errorMessage = 'Syntax error on line ' + str(self._lineNumber) + '. Missing opening parentheses "(".'
                    self._errorMessages.append([self._lineNumber, errorMessage])
                
                if self.IsOperator(prefixExpression) and tempToken != '':
                    if prefixExpression == '-':
                        prefixExpression = '-0 ' + tempToken + ' '
                    else:
                        self._errorCount += 1
                        errorMessage = 'Syntax error on line ' + str(self._lineNumber) + '. Invalid expression.'
                        self._errorMessages.append([self._lineNumber, errorMessage])
                
                elif tempToken != '': 
                    prefixExpression += tempToken + ' '
                
                else: #All other cases
                    pass
                return prefixExpression
                        
            if expression[i] == '(':
                openParenthesesCount += 1
                if openParenthesesCount == 1:
                    continue
                
            elif expression[i] == ')':
                openParenthesesCount -= 1

                if openParenthesesCount == 0:
                    parenPrefixExpression = self.FindPrefixExpression(parenExpression + ';')
                    tempToken = parenPrefixExpression
                    parenPrefixExpression = ''
                    continue
            
            if openParenthesesCount > 0:
                parenExpression += expression[i]
                continue
            
            #If it is an operator
            if self.IsOperator(expression[i]):

                #Check tempToken to make sure it is a valid Variable or number
                if tempToken != '':
                    if not self.IsNumber(tempToken) and not self.IsNegativeNumber(tempToken) and not self.IsFloatingPointNumber(tempToken) and not self.IsNegativeFloatingPointNumber(tempToken):
                        if not self.VariableNameExists(tempToken):
                            self._errorCount += 1
                            errorMessage = 'Error on line ' + str(self._lineNumber) + '. Variable \"' + token + '\" does not exist.'
                            self._errorMessages.append([self._lineNumber, errorMessage])
                        
                        elif not self.VariableHasValue(tempToken):
                            self._errorCount += 1
                            errorMessage = 'Error on line ' + str(self._lineNumber) + '. Variable \"' + token + '\" does not have a value.'
                            self._errorMessages.append([self._lineNumber, errorMessage])

                if expression[i] == '-' and i != 0 and self.IsOperator(expression[i - 1]): #This is a negative number and should be added to the tempToken
                    prefixExpression += '-0 '
                    self._operatorCount += 1
                elif expression[i] == '-' and tempToken == '': #Handles negative numbers right after the equals sign
                    prefixExpression = expression[i] + prefixExpression + '0 '
                    tempToken = ''
                    previousOperator = expression[i]
                    self._operatorCount += 1
                else:
                    if expression[i] == '^':
                        #previousOperatorIndex = len(prefixExpression)
                        prefixExpression = prefixExpression + expression[i] + tempToken + ' '
                    
                    elif expression[i] == '*': 
                        if previousOperator == '^' or previousOperator == '*' or previousOperator == '':
                            prefixExpression = expression[i] + prefixExpression + tempToken + ' ' # X^7*5 = *^X 7 5 or X * 7 * 5 = **X 7 5  
                            #previousOperatorIndex = 0
                        elif previousOperator != '': # + or - 
                            #previousOperatorIndex = len(prefixExpression)
                            prefixExpression = prefixExpression + expression[i] + tempToken + ' ' #X-7*5 = -X*7 5
                    else: # + or -
                        prefixExpression = expression[i] + prefixExpression + tempToken + ' '
                        #previousOperatorIndex = 0
                    tempToken = ''
                    previousOperator = expression[i]
                    self._operatorCount += 1
            else:
                tempToken += expression[i]
            
            #li = '' #((<NUMBER> | -<NUMBER>) | <VARIABLE NAME><REF>) | <PAREN>
                #<REF> ::= <AP> | e
                #<AP> ::= [<EXP><ST>]
                #<ST> ::= ,<EXP><ST> | e

    def GenerateAssemblyFile(self, assemblyFile):
        initilaizedValues = self._initializedValues
        uninitilaizedValues = self._uninitializedValues
        operations = self._operations
        exponentiateCount = 0
        afterProceduresPrinted = False
        nestCount = 0
        register = 'edi'

        assemblyFile.write('global _main\n')
        assemblyFile.write('EXPORT _main\n')
        assemblyFile.write('\n')
        assemblyFile.write('extern _printf\n')
        assemblyFile.write('extern _scanf\n')
        assemblyFile.write('extern _ExitProcess@4\n')
        assemblyFile.write('\n')

        #Initialized Variables
        if len(initilaizedValues) != 0:
            assemblyFile.write('section .data USE32\n')
            assemblyFile.write('\n')
            
            for initVar in initilaizedValues:
                
                if self._deadCodeElimination:
                    if not initVar[1] in self._variablesUsed:
                        continue
                
                assemblyFile.write('\t')
                
                if initVar[0].find('stringPrinter') != -1:
                    assemblyFile.write(str(initVar[0]) + '\t' + 'db ' + str(initVar[1]) + ',0\n')
                elif initVar[0].find('numberPrinter') != -1:
                    assemblyFile.write(str(initVar[0]) + '\t' + 'db ' + str(initVar[1]) + ',0x0d,0x0a,0\n')
                elif initVar[0].find('floatPrinter') != -1:
                    assemblyFile.write(str(initVar[0]) + '\tdb ' + str(initVar[1]) + ',0x0d,0x0a,0\n')
                elif initVar[0] == 'num':
                    assemblyFile.write(str(initVar[1]) + '\t\t' + 'dd\t' + str(initVar[2]) + '\n')
                else:
                    assemblyFile.write(str(initVar[1]) + '\t' + 'db ' + str(initVar[2]) + ',0x0d,0x0a,0\n')
            
            assemblyFile.write('\n')
        
        #Uninitialized Variables
        assemblyFile.write('section .bss USE32\n')
        assemblyFile.write('\n')

        if len(self._procedures) != 0:
            # self._procedureParameters.append(['num', variable, 'Has value'])
            for parameter in self._procedureParameters:
                assemblyFile.write('\t' + str(parameter[1]) + '\t\t' + 'resd\t' + '1' + '\n')
        
        if self._varFloatCount > 0:
            assemblyFile.write('\tfloatExpressionLeft\tresb\t4\n')
            assemblyFile.write('\tfloatExpressionRight\tresb\t4\n')

        if len(uninitilaizedValues) != 0:
            for uninitVar in uninitilaizedValues:
                
                if self._deadCodeElimination:
                    if not uninitVar[1] in self._variablesUsed:
                        continue

                if uninitVar[0].find('num_array') != -1:
                    sizeOfArrayInBytes = uninitVar[2]*4
                    assemblyFile.write('\t' + str(uninitVar[1] + '\t' + 'resb' + '\t' + str(sizeOfArrayInBytes) + '\n'))
                elif uninitVar[0] == 'float':
                    assemblyFile.write('\t' + str(uninitVar[1]) + '\t\t' + 'resb\t' + '4' + '\n')
                elif uninitVar[0] == 'string':
                    assemblyFile.write('\t' + str(uninitVar[1]) + '\t\t' + 'resb\t' + '128' + '\n')
                else:
                    assemblyFile.write('\t' + str(uninitVar[1]) + '\t\t' + 'resd\t' + '1' + '\n')
            
        assemblyFile.write('\n')

        #Main
        assemblyFile.write('section .code USE32\n')
        assemblyFile.write('\n')
        assemblyFile.write('_main:\n')
        assemblyFile.write('\n')

        if len(self._procedures) > 0:
            assemblyFile.write('\tjmp\tafterprocedures\n')
            assemblyFile.write('\n')
        
        assemblyFile.write('\tmov\tecx,\t0\n') # For string assignments and concatenation
        
        for operation in operations:

            if self._assemblyProcedureCount == len(self._procedures) and len(self._procedures) > 0 and  not afterProceduresPrinted:
                afterProceduresPrinted = True
                assemblyFile.write('afterprocedures:\n')
                assemblyFile.write('\n')

            if operation[0] == 'numVariableAssignment':
                if operation[3].find('_np_') != -1:
                    assemblyFile.write('\tmov\teax,\tDWORD[' + operation[3] + ']\n')
                    #self.AssemblyCodeForNumOrVar(operation[1], assemblyFile)
                    assemblyFile.write('\tmov\tDWORD[eax],\t')
                    if self.IsNumber(operation[1]) or self.IsNegativeNumber(operation[1]):
                        assemblyFile.write(operation[1] + '\n')
                    else:
                        assemblyFile.write('DWORD[' + operation[1] + ']\n')
                else:
                    assemblyFile.write('\tmov\t' + register + ',\t')
                    #self.AssemblyCodeForNumOrVar(operation[1], assemblyFile)
                    if self.IsNumber(operation[1]) or self.IsNegativeNumber(operation[1]):
                        assemblyFile.write(operation[1] + '\n')
                    else:
                        assemblyFile.write('DWORD[' + operation[1] + ']\n')
                    assemblyFile.write('\tmov\tDWORD[' + operation[3] + '],\t' + register + '\n')
            
            if operation[0] == 'floatVariableAssignment':
                # self._operations.append(['floatVariableAssignment', result, '', self.GetVariableName(variableName)])
                if self.IsFloatingPointNumber(operation[1]) or self.IsNegativeFloatingPointNumber(operation[1]):
                    assemblyFile.write('\tmov\tDWORD[' + operation[3] + '],\t__float32__(' + operation[1] + ')\n')
                else:
                    assemblyFile.write('\tfld\tQWORD[' + operation[1] + ']\n')
                    assemblyFile.write('\tfstp\tDWORD[' + operation[3] + ']\n')
            
            elif operation[0] == 'stringVariableAssignment':
                # self._operations.append(['stringVariableAssignment', variable1, '', variable])
                tempRegister = 'esi'
                if register == 'esi':
                    tempRegister = 'edx'
                elif register == 'edx':
                    tempRegister = 'ecx'

                assemblyFile.write('\tcld\n')
                assemblyFile.write('\tmov\t' + tempRegister + ',\t' + operation[1] + '\n')
                assemblyFile.write('\tmov\t' + register + ',\t' + operation[3] + '\n')
                assemblyFile.write('copy' + str(self._stringOperationCount) + ':\n')
                assemblyFile.write('\tmov\tcl,\tbyte[' + tempRegister + ']\n')
                assemblyFile.write('\tadd\tcl,\t1\n')
                assemblyFile.write('\tmovsb\n')
                assemblyFile.write('\tloop copy' + str(self._stringOperationCount) + '\n')
                self._stringOperationCount += 1

            elif operation[0] == 'stringConcatenationAssignment':
                # self._operations.append(['stringConcatenationAssignment', tempOperand1, tempOperand2, variable])
                tempRegister = 'esi'
                if register == 'esi':
                    tempRegister = 'edx'
                elif register == 'edx':
                    tempRegister = 'ecx'

                assemblyFile.write('\tcld\n')
                assemblyFile.write('\tmov\t' + tempRegister + ',\t' + operation[1] + '\n')
                assemblyFile.write('\tmov\t' + register + ',\t' + operation[3] + '\n')
                assemblyFile.write('copy' + str(self._stringOperationCount) + ':\n')
                assemblyFile.write('\tmov\tcl,\tbyte[' + tempRegister + ']\n')
                assemblyFile.write('\tadd\tcl,\t1\n')
                assemblyFile.write('\tmovsb\n')
                assemblyFile.write('\tloop\tcopy' + str(self._stringOperationCount) + '\n')
                self._stringOperationCount += 1

                #_stringConcatCount
                assemblyFile.write('\tdec\t' + register + '\n')
                assemblyFile.write('\tdec\t' + register + '\n')
                assemblyFile.write('\tdec\t' + register + '\n')
                assemblyFile.write('\tmov\t' + tempRegister + ',\t' + operation[2] + '\n')
                assemblyFile.write('concatinate' + str(self._stringConcatCount) + ':\n')
                assemblyFile.write('\tmov\tcl,\tbyte[' + tempRegister + ']\n')
                assemblyFile.write('\tadd\tcl,\t1\n')
                assemblyFile.write('\tmovsb\n')
                assemblyFile.write('\tloop\tconcatinate' + str(self._stringConcatCount) + '\n')
                self._stringConcatCount += 1
            
            elif operation[0] == 'arrayOffset':
                # self._operations.append(['arrayOffset', delta[j], arrayList[j]])
                tempRegister = 'esi'
                if register == 'esi':
                    tempRegister = 'edx'
                elif register == 'edx':
                    tempRegister = 'ecx'

                assemblyFile.write('\tmov\t' + tempRegister + ',\t' + str(operation[1]) + '\n')
                assemblyFile.write('\timul\t' + tempRegister + ',\t' + str(operation[2]) + '\n')
                assemblyFile.write('\tadd\t' + register + ',\t' + tempRegister + '\n')
            
            elif operation[0] == 'arrayOffsetVariable':
                # self._operations.append(['arrayOffsetVariable', delta[j], arrayList[j]])
                tempRegister = 'esi'
                if register == 'esi':
                    tempRegister = 'edx'
                elif register == 'edx':
                    tempRegister = 'ecx'

                assemblyFile.write('\tmov\t' + tempRegister + ',\t' + str(operation[1]) + '\n')
                assemblyFile.write('\timul\t' + tempRegister + ',\tDWORD[' + str(operation[2]) + ']\n')
                assemblyFile.write('\tadd\t' + register + ',\t' + tempRegister + '\n')

            elif operation[0] == 'allocateToArray':
                # self._operations.append(['allocateToArray', array[4], 4, array[1], result])
                assemblyFile.write('\tsub\t' + register + ',\t' + str(operation[1]) + '\n')
                assemblyFile.write('\timul\t' + register + ',\t' + str(operation[2]) + '\n')
                assemblyFile.write('\tadd\t' + register + ',\t' + operation[3] + '\n')
                assemblyFile.write('\tmov\tDWORD[' + register + '],\t' + operation[4] + '\n')
            
            elif operation[0] == 'allocateValueFromVariableToArray':
                # self._operations.append(['allocateToArray', array[4], 4, array[1], result])
                tempRegister = 'esi'
                if register == 'esi':
                    tempRegister = 'edx'
                elif register == 'edx':
                    tempRegister = 'ecx'
                assemblyFile.write('\tsub\t' + register + ',\t' + str(operation[1]) + '\n')
                assemblyFile.write('\timul\t' + register + ',\t' + str(operation[2]) + '\n')
                assemblyFile.write('\tadd\t' + register + ',\t' + operation[3] + '\n')
                assemblyFile.write('\tmov\t' + tempRegister + ',\tDWORD[' + operation[4] + ']\n')
                assemblyFile.write('\tmov\tDWORD[' + register + '],\t' + tempRegister + '\n')

            elif operation[0] == 'add':
                assemblyFile.write('\tmov\t' + register + ',\t')
                self.AssemblyCodeForNumOrVar(operation[1], assemblyFile)
                assemblyFile.write('\tadd\t' + register + ',\t')
                self.AssemblyCodeForNumOrVar(operation[2], assemblyFile)
                assemblyFile.write('\tmov\tDWORD[' + operation[3] + '],\t' + register + '\n')
            
            elif operation[0] == 'addFloat':
                if self.VariableNameExists(operation[1]):
                    if self.GetVariableType(operation[1]) == 'num':
                        assemblyFile.write('\tfild\tDWORD['+ operation[1] + ']\n')
                    elif self.GetVariableType(operation[1]) == 'float':
                        assemblyFile.write('\tfld\tDWORD['+ operation[1] + ']\n')
                else:
                    if self.IsNumber(operation[1]) or self.IsNegativeNumber(operation[1]):
                        assemblyFile.write('\tmov\tDWORD[floatExpressionLeft],\t' + operation[1] + '\n')
                        assemblyFile.write('\tfild\tDWORD[floatExpressionLeft]\n')
                    else:
                        assemblyFile.write('\tmov\tDWORD[floatExpressionLeft],\t__float32__(' + operation[1] + ')\n')
                        assemblyFile.write('\tfld\tDWORD[floatExpressionLeft]\n')

                if self.VariableNameExists(operation[2]):
                    if self.GetVariableType(operation[2]) == 'num':
                        assemblyFile.write('\tfild\tDWORD['+ operation[2] + ']\n')
                    elif self.GetVariableType(operation[2]) == 'float':
                        assemblyFile.write('\tfld\tDWORD['+ operation[2] + ']\n')
                else:
                    if self.IsNumber(operation[2]) or self.IsNegativeNumber(operation[2]):
                        assemblyFile.write('\tmov\tDWORD[floatExpressionRight],\t' + operation[2] + '\n')
                        assemblyFile.write('\tfild\tDWORD[floatExpressionRight]\n')
                    else:
                        assemblyFile.write('\tmov\tDWORD[floatExpressionRight],\t__float32__(' + operation[2] + ')\n')
                        assemblyFile.write('\tfld\tDWORD[floatExpressionRight]\n')
                
                assemblyFile.write('\tfadd\n')
                assemblyFile.write('\tfstp\tQWORD[' + operation[3] + ']\n')
            
            elif operation[0] == 'subtract':
                assemblyFile.write('\tmov\t' + register + ',\t')
                self.AssemblyCodeForNumOrVar(operation[1], assemblyFile)
                assemblyFile.write('\tsub\t' + register + ',\t')
                self.AssemblyCodeForNumOrVar(operation[2], assemblyFile)
                assemblyFile.write('\tmov\tDWORD[' + operation[3] + '],\t' + register + '\n')
            
            elif operation[0] == 'subtractFloat':
                if self.VariableNameExists(operation[1]):
                    if self.GetVariableType(operation[1]) == 'num':
                        assemblyFile.write('\tfild\tDWORD['+ operation[1] + ']\n')
                    elif self.GetVariableType(operation[1]) == 'float':
                        assemblyFile.write('\tfld\tDWORD['+ operation[1] + ']\n')
                else:
                    if self.IsNumber(operation[1]) or self.IsNegativeNumber(operation[1]):
                        assemblyFile.write('\tmov\tDWORD[floatExpressionLeft],\t' + operation[1] + '\n')
                        assemblyFile.write('\tfild\tDWORD[floatExpressionLeft]\n')
                    else:
                        assemblyFile.write('\tmov\tDWORD[floatExpressionLeft],\t__float32__(' + operation[1] + ')\n')
                        assemblyFile.write('\tfld\tDWORD[floatExpressionLeft]\n')

                if self.VariableNameExists(operation[2]):
                    if self.GetVariableType(operation[2]) == 'num':
                        assemblyFile.write('\tfild\tDWORD['+ operation[2] + ']\n')
                    elif self.GetVariableType(operation[2]) == 'float':
                        assemblyFile.write('\tfld\tDWORD['+ operation[2] + ']\n')
                else:
                    if self.IsNumber(operation[2]) or self.IsNegativeNumber(operation[2]):
                        assemblyFile.write('\tmov\tDWORD[floatExpressionRight],\t' + operation[2] + '\n')
                        assemblyFile.write('\tfild\tDWORD[floatExpressionRight]\n')
                    else:
                        assemblyFile.write('\tmov\tDWORD[floatExpressionRight],\t__float32__(' + operation[2] + ')\n')
                        assemblyFile.write('\tfld\tDWORD[floatExpressionRight]\n')
                
                assemblyFile.write('\tfsub\n')
                assemblyFile.write('\tfstp\tQWORD[' + operation[3] + ']\n')

            elif operation[0] == 'bitShift':
                assemblyFile.write('\tmov\t' + register + ',\t')
                self.AssemblyCodeForNumOrVar(operation[2], assemblyFile)
                assemblyFile.write('\tsal\t' + register + ',\t')
                self.AssemblyCodeForNumOrVar(operation[1], assemblyFile)
                assemblyFile.write('\tmov\tDWORD[' + operation[3] + '],\t' + register + '\n')

            elif operation[0] == 'negativeBitShift':
                assemblyFile.write('\tmov\t' + register + ',\t')
                self.AssemblyCodeForNumOrVar(operation[2], assemblyFile)
                assemblyFile.write('\timul\t' + register + ',\t-1\t')
                assemblyFile.write('\tsal\t' + register + ',\t')
                self.AssemblyCodeForNumOrVar(operation[1], assemblyFile)
                assemblyFile.write('\tmov\tDWORD[' + operation[3] + '],\t' + register + '\n')

            elif operation[0] == 'multiply':
                assemblyFile.write('\tmov\t' + register + ',\t')
                self.AssemblyCodeForNumOrVar(operation[1], assemblyFile)
                assemblyFile.write('\timul\t' + register + ',\t')
                self.AssemblyCodeForNumOrVar(operation[2], assemblyFile)
                assemblyFile.write('\tmov\tDWORD[' + operation[3] + '],\t' + register + '\n')
            
            elif operation[0] == 'multiplyFloat':
                if self.VariableNameExists(operation[1]):
                    if self.GetVariableType(operation[1]) == 'num':
                        assemblyFile.write('\tfild\tDWORD['+ operation[1] + ']\n')
                    elif self.GetVariableType(operation[1]) == 'float':
                        assemblyFile.write('\tfld\tDWORD['+ operation[1] + ']\n')
                else:
                    if self.IsNumber(operation[1]) or self.IsNegativeNumber(operation[1]):
                        assemblyFile.write('\tmov\tDWORD[floatExpressionLeft],\t' + operation[1] + '\n')
                        assemblyFile.write('\tfild\tDWORD[floatExpressionLeft]\n')
                    else:
                        assemblyFile.write('\tmov\tDWORD[floatExpressionLeft],\t__float32__(' + operation[1] + ')\n')
                        assemblyFile.write('\tfld\tDWORD[floatExpressionLeft]\n')

                if self.VariableNameExists(operation[2]):
                    if self.GetVariableType(operation[2]) == 'num':
                        assemblyFile.write('\tfild\tDWORD['+ operation[2] + ']\n')
                    elif self.GetVariableType(operation[2]) == 'float':
                        assemblyFile.write('\tfld\tDWORD['+ operation[2] + ']\n')
                else:
                    if self.IsNumber(operation[2]) or self.IsNegativeNumber(operation[2]):
                        assemblyFile.write('\tmov\tDWORD[floatExpressionRight],\t' + operation[2] + '\n')
                        assemblyFile.write('\tfild\tDWORD[floatExpressionRight]\n')
                    else:
                        assemblyFile.write('\tmov\tDWORD[floatExpressionRight],\t__float32__(' + operation[2] + ')\n')
                        assemblyFile.write('\tfld\tDWORD[floatExpressionRight]\n')
                
                assemblyFile.write('\tfmul\n')
                assemblyFile.write('\tfstp\tQWORD[' + operation[3] + ']\n')

            elif operation[0] == 'exponentiate':
                assemblyFile.write('\txor\t' + register + ',\t' + register + '\n')
                assemblyFile.write('\tmov\teax,\t0x00000001\n')
                assemblyFile.write('_exp_top_' + str(exponentiateCount) + ':\n')
                assemblyFile.write('\tcmp\t' + register + ',\t')
                self.AssemblyCodeForNumOrVar(operation[2], assemblyFile)
                assemblyFile.write('\tjz\t_exp_out_' + str(exponentiateCount) + '\n')
                assemblyFile.write('\timul\teax,\t')
                self.AssemblyCodeForNumOrVar(operation[1], assemblyFile)
                assemblyFile.write('\tinc\t' + register + '\n')
                assemblyFile.write('\tjmp\t_exp_top_' + str(exponentiateCount) + '\n')
                assemblyFile.write('_exp_out_' + str(exponentiateCount) + ':\n')
                assemblyFile.write('\tmov\tDWORD[' + operation[3] + '],\teax\n')
                exponentiateCount += 1
        
            elif operation[0] == 'write':
                if self.GetVariableType(operation[1]) == 'num':
                    assemblyFile.write('\tpush\tDWORD[' + operation[1] +']\n')
                    assemblyFile.write('\tpush\tnumberPrinter\n')

                elif self.IsNumber(operation[1]) or self.IsNegativeNumber(operation[1]):
                    assemblyFile.write('\tpush\t' + operation[1] +'\n')
                    assemblyFile.write('\tpush\tnumberPrinter\n')

                elif self.GetVariableType(operation[1]) == 'numPointer':
                    assemblyFile.write('\tmov\teax,\tDWORD[' + operation[1] + ']\n')
                    assemblyFile.write('\tpush\tDWORD[eax]\n')
                    assemblyFile.write('\tpush\tnumberPrinter\n')
                    
                elif self.GetVariableType(operation[1]) == 'float':
                    assemblyFile.write('\tfld\tDWORD[' + operation[1] + ']\n')
                    assemblyFile.write('\tfstp\tQWORD[esp]\n')
                    assemblyFile.write('\tpush\tfloatPrinter\n')
                
                elif self.IsFloatingPointNumber(operation[1]) or self.IsNegativeFloatingPointNumber(operation[1]):
                    assemblyFile.write('\tfld\t' + operation[1] + '\n')
                    assemblyFile.write('\tfstp\tQWORD[esp]\n')
                    assemblyFile.write('\tpush\tfloatPrinter\n')

                else:
                    assemblyFile.write('\tpush\t' + operation[1] + '\n')
                    assemblyFile.write('\tpush\tstringPrinter\n')

                assemblyFile.write('\tcall\t_printf\n')
                assemblyFile.write('\tadd\tesp,\t0x08\n')
            
            elif operation[0] == 'writeItemFromArray':
                # self._operations.append(['writeItemFromArray', array[4], 4, array[1]])
                assemblyFile.write('\tsub\t' + register + ',\t' + str(operation[1]) + '\n')
                assemblyFile.write('\timul\t' + register + ',\t' + str(operation[2]) + '\n')
                assemblyFile.write('\tadd\t' + register + ',\t' + operation[3] + '\n')
                assemblyFile.write('\tpush\tDWORD[' + register + ']\n')
                assemblyFile.write('\tpush\tnumberPrinter\n')
                assemblyFile.write('\tcall\t_printf\n')
                assemblyFile.write('\tadd\tesp,\t0x08\n')

            elif operation[0] == 'read':
                assemblyFile.write('\tpusha\n')
                assemblyFile.write('\tpush\t' + operation[1] + '\n')
                assemblyFile.write('\tpush\tdword int_format\n')
                assemblyFile.write('\tcall\t_scanf\n')
                assemblyFile.write('\tadd\tesp,\t0x04\n')
                assemblyFile.write('\tpopa\n')

            elif operation[0] == 'beginForLoop':
                nestCount += 1
                if nestCount == 1:
                    register = 'esi'
                elif nestCount == 2:
                    register = 'edx'

                assemblyFile.write('_loop_start_' + str(operation[1]) +':\n')
                assemblyFile.write('\t;termination condition\n')
                assemblyFile.write('\tmov\t' + register + ',\tDWORD[' + operation[3] + ']\n')
                assemblyFile.write('\tcmp\tDWORD[' + operation[2] + '],\t' + register + '\n')
                assemblyFile.write('\tjg\t_loop_end_' + str(operation[1]) + '\n')
                assemblyFile.write('\n\n\t; block\n')

            elif operation[0] == 'endForLoop':

                assemblyFile.write('\t; end block\n')
                assemblyFile.write('\tmov ' + register + ',\t' + 'DWORD[' + operation[3] + ']\n')
                assemblyFile.write('\tadd\tDWORD[' + operation[2] + '],\t' + register + '\n')
                assemblyFile.write('\tjmp\t_loop_start_' + str(operation[1]) + '\n')
                assemblyFile.write('\n\n\t; block\n')
                assemblyFile.write('_loop_end_' + str(operation[1]) + ':\n')

                nestCount -= 1

            elif operation[0] == 'beginIfStatement':
                # self._operations.append(['beginIfStatement', self._ifCount, left, right, relationalOperator])
                operator = ''
                nestCount += 1
                if nestCount == 1:
                    register = 'esi'
                elif nestCount == 2:
                    register = 'edx'

                assemblyFile.write('\t;if condition\n')
                assemblyFile.write('\tmov\t' + register + ',\t')
                self.AssemblyCodeForNumOrVar(operation[2], assemblyFile)
                assemblyFile.write('\tcmp\t' + register + ',\t')
                self.AssemblyCodeForNumOrVar(operation[3], assemblyFile)
                if operation[4] == '==':
                    operator = 'jne'
                elif operation[4] == '!=':
                    operator = 'je'
                elif operation[4] == '<':
                    operator = 'jge'
                elif operation[4] == '<=':
                    operator = 'jg'
                elif operation[4] == '>':
                    operator = 'jle'
                elif operation[4] == '>=':
                    operator = 'jl'
                assemblyFile.write('\t' + operator + '\t_end_if_' + str(operation[1]) + '\n')
                assemblyFile.write('\n\n\t; block\n')
            
            elif operation[0] == 'endIfStatement':
                # self._operations.append(['beginIfStatement', self._ifCount, left, right, relationalOperator])
                assemblyFile.write('_end_if_' + str(operation[1]) + ':\n')
                assemblyFile.write('\n\n\t; block\n')

            elif operation[0] == 'elseBegin':
                # elseOperation = ['elseBegin', self._elseCount]
                assemblyFile.write('\tjmp\t_end_else_' + str(operation[1]) + '\n')
            
            elif operation[0] == 'endElse':
                assemblyFile.write('_end_else_' + str(operation[1]) + ':\n')

            elif operation[0] == 'switch':
                assemblyFile.write('\tmov\t' + register + ',\t' + 'DWORD[' + str(operation[1]) + ']\n')
            
            elif operation[0] == 'endSwitch':
                assemblyFile.write('_end_switch_' + str(operation[1]) + ':\n')

            elif operation[0] == 'case':
                assemblyFile.write('\tcmp\t' + register + ',\t')
                self.AssemblyCodeForNumOrVar(operation[2], assemblyFile)
                assemblyFile.write('\tjnz\t_end_case_' + str(operation[1]) + '\n')
                nestCount += 1
                if nestCount == 1:
                    register = 'esi'
                elif nestCount == 2:
                    register = 'edx'
            
            elif operation[0] == 'endCase':
                assemblyFile.write('\tjmp\t_end_switch_' + str(operation[2]) + '\n')
                assemblyFile.write('_end_case_' + str(operation[1]) + ':\n')
                nestCount -= 1
                if nestCount == 0:
                    register = 'edi'
                if nestCount == 1:
                    register = 'esi'
                elif nestCount == 2:
                    register = 'edx'

            elif operation[0] == 'procedureDeclaration':
                # self._operations.append('procedureDeclaration', procedureName, variableParameterList)
                #    parameterToAdd = [procedureName, variableType, variable, passByReference]
                #        variableParameterList.append(parameterToAdd)
                assemblyFile.write(operation[1] + ':\n')
                variableCount = len(operation[2])
                for variableParam in operation[2]:
                    index = variableCount*4
                    assemblyFile.write('\tmov\teax,\tDWORD[esp+' + str(index) + ']\n') # May need to deal with multiple types later.
                    assemblyFile.write('\tmov\tDWORD[' + variableParam[2] + '],\teax\n')
                    assemblyFile.write('\n')
                    variableCount -= 1
            
            elif operation[0] == 'endProcedure' or operation == 'endProcedure':
                assemblyFile.write('\tret\n')
                assemblyFile.write('\t; ------- End of Procedure ----------\n')
                assemblyFile.write('\n')
                self._assemblyProcedureCount += 1

            #self._operations.append(['procedureCall', procedureName, variableParameterList])
            elif operation[0] == 'procedureCall':
                # Pass in parameters
                for variableParameter in operation[2]:
                    if variableParameter[2]: # Pass by Reference
                        assemblyFile.write('\tpush\t' + variableParameter[1] + '\n')
                    else:
                        assemblyFile.write('\tpush\tDWORD[' + variableParameter[1] + ']\n')
                assemblyFile.write('\tcall\t' + operation[1] + '\n')

            elif operation[0] == 'clearRegister':
                assemblyFile.write('\txor\t' + register + ',\t' + register + '\n')

            assemblyFile.write('\n')

            
            #newOperation = ['beginForLoop', forLoop[0], forLoop[1], forLoop[2]]

            #_loop_start_0:
            #   ;termination condition
            #   cmp	DWORD[_n_1_i],	edi		; compare loop counter to end val
            #   jg	_loop_end_0
    

        # def EndForLoop(self):
        #     forLoop = self.forLoops[self.forloopCount - 1]
        #     newOperation = ['endForLoop', forLoop[0], forLoop[1], forLoop[3]]

        assemblyFile.write('\n')

        #End of file
        assemblyFile.write('exit:\n')
        assemblyFile.write('\tmov\teax, 0x0\n')
        assemblyFile.write('\tcall\t_ExitProcess@4\n')

    def GenerateErrorFile(self, errorFile, errorMessages):
        
        numberOfErrors = 0

        if errorMessages[0][1] != 'valid':
            numberOfErrors = len(errorMessages)

        for errorMessage in errorMessages:
            errorFile.write('\t' + errorMessage[1] + '\n')
        
        if numberOfErrors == 0:
            errorFile.write('\n\tNo errors were found.\n')
        elif numberOfErrors == 1:
            errorFile.write('\n\t(' + str(len(errorMessages)) + ') error was found.\n')
        elif numberOfErrors > 1: 
            errorFile.write('\n\t(' + str(len(errorMessages)) + ') errors were found.\n')

    def GetArray(self, arrayName):
        listVariableName = ''

        for i in range(0, len(self._uninitializedValues)):

            _count = 0
            for j in range(0, len(self._uninitializedValues[i][1])):
                if self._uninitializedValues[i][1][j] == '_':
                    _count += 1
                if _count == 3:
                    listVariableName = self._uninitializedValues[i][1][j + 1 : len(self._uninitializedValues[i][1])]
                    break

            if listVariableName == arrayName or self._uninitializedValues[i][1] == arrayName:
                return self._uninitializedValues[i]
    

    def GetProcedure(self, procedureName):
        #self._procedures.append([procedureName, variableParameterList])
        for procedure in self._procedures:
            if procedure[0] == procedureName:
                return procedure

    def GetVariableName(self, variableName):
        listVariableName = ''

        for i in range(0, len(self._initializedValues)):

            _count = 0
            for j in range(0, len(self._initializedValues[i][1])):
                if self._initializedValues[i][1][j] == '_':
                    _count += 1
                if _count == 3:
                    listVariableName = self._initializedValues[i][1][j + 1 : len(self._initializedValues[i][1])]
                    break

            if listVariableName == variableName or variableName == self._initializedValues[i][1]:
                return self._initializedValues[i][1]

        for i in range(0, len(self._uninitializedValues)):

            _count = 0
            for j in range(0, len(self._uninitializedValues[i][1])):
                if self._uninitializedValues[i][1][j] == '_':
                    _count += 1
                if _count == 3:
                    listVariableName = self._uninitializedValues[i][1][j + 1 : len(self._uninitializedValues[i][1])]
                    break

            if listVariableName == variableName or variableName == self._uninitializedValues[i][1]:
                #if self._uninitializedValues[i][2] != 'no value':
                return self._uninitializedValues[i][1]
    
    def GetVariableType(self, variableName):
        listVariableName = ''

        for i in range(0, len(self._initializedValues)):

            _count = 0
            for j in range(0, len(self._initializedValues[i][1])):
                if self._initializedValues[i][1][j] == '_':
                    _count += 1
                if _count == 3:
                    listVariableName = self._initializedValues[i][1][j + 1 : len(self._initializedValues[i][1])]
                    break

            if listVariableName == variableName or variableName == self._initializedValues[i][1]:
                return self._initializedValues[i][0]

        for i in range(0, len(self._uninitializedValues)):

            _count = 0
            for j in range(0, len(self._uninitializedValues[i][1])):
                if self._uninitializedValues[i][1][j] == '_':
                    _count += 1
                if _count == 3:
                    listVariableName = self._uninitializedValues[i][1][j + 1 : len(self._uninitializedValues[i][1])]
                    break

            if listVariableName == variableName or variableName == self._uninitializedValues[i][1]:
                return self._uninitializedValues[i][0]


    def HasValidVariableSyntax(self, variableName): #boolean
        #<VARIABLE NAME> ::= <LETTER><VARIABLE NAME PRIME>
        #<VARIABLE NAME PRIME> ::= <VAR CHARACTER><VARIABLE NAME PRIME> | e
        for i in range(0,len(variableName)):
            if i == 0:
                if not str.isalpha(variableName[i]):
                    return False
            else:
                if not self.IsValidVarCharacter(variableName[i]):
                    return False
        return True

    def HasValidWordSyntax(self, expression):
        # <WORD> ::= <LETTER><GAMMA>
        # <GAMMA> ::= e | <CHARACTER><GAMMA>
        # <CHARACTER> ::= <LETTER> | <DIGIT> | . | , | < | > | ? | { | } | _  | ! | @ | # | $ | & | "space" (i.e a space: " ") | ~ | ` | :
        quotationCount = 0

        for i in range(0, len(expression)):

            if expression[i] == '"':
                quotationCount += 1
            elif not self.IsValidCharacter(expression[i]):
                return False
            
        if quotationCount == 2:
            return True
        else:
            return False

    def IsFloatingPointNumber(self, number):
        periodFound = False
        right = ''
        left = ''
        if number != '':
            for i in range(0, len(number)):
                if number[i] == '.':
                    periodFound = True
                    continue
                if not periodFound:
                    left += number[i]
                else:
                    right += number[i]
            
            if left.isnumeric() and right.isnumeric():
                return True
            else:
                return False
        else:
            return False
    
    def IsNegativeFloatingPointNumber(self, number):
        periodFound = False
        right = ''
        left = ''
        if number != '':
            if number[0] == '-':
                for i in range(1, len(number)):
                    if number[i] == '.':
                        periodFound = True
                        continue
                    if not periodFound:
                        left += number[i]
                    else:
                        right += number[i]
            else:
                return False
            
            if left.isnumeric() and right.isnumeric():
                return True
            else:
                return False
        else:
            return False

    def IsNegativeNumber(self, number):
        if number != '':
            return number[0] == '-' and number[1:len(number)].isnumeric()
        else:
            return False

    def IsNegativeNumberIndex(self, index):
        for negNumIndex in self._negativeNumberIndexes:
            if index == negNumIndex:
                return True
        return False

    def IsNumber(self, number):
        if number != '':
            return number.isnumeric()
        else:
            return False

    def IsValidCharacter(self, char):
        # <CHARACTER> ::= <LETTER> | <DIGIT> | . | , | < | > | ? | { | } | _  | ! | @ | # | $ | & | "space" (i.e a space: " ") | ~ | ` | :
        if char == '\'' or char == '"' or char == '\\':
            return False
        else:
            return True

    def IsOperator(self, char):
        return char == '+' or char == '-' or char == '*' or char == '/' or char == '^'
    
    def GetStringConstantIfExists(self, stringConstant):
        
        for item in self._initializedValues:
            if item[1] == stringConstant:
                return item[0]
        return ''

    def IsValidVarCharacter(self, varChar): #boolean
        #<VAR CHARACTER> ::= <LETTER> | <DIGIT> | _
        if str.isalpha(varChar) or str.isnumeric(varChar) or varChar == '_':
            return True
        else:
            return False

    def NewCurlyBraceFound(self):

        if self._switchNeedsCurlyBrace:
            self._openCurlyBrace.append(['switch', self._switchCount])
            self._currentSwitch.append(self._switchCount)
            self._switchCount += 1
            self._switchNeedsCurlyBrace = False

        elif self._caseNeedsCurlyBrace:
            self._openCurlyBrace.append(['case', self._caseCount])
            self._caseCount += 1
            self._caseNeedsCurlyBrace = False

        elif self._defaultCaseNeedsCurlyBrace:
            self._openCurlyBrace.append(['defaultCase', None])
            self._defaultCaseNeedsCurlyBrace = False

        elif self._ifNeedsCurlyBrace:
            self._openCurlyBrace.append(['if', self._ifCount])
            self._currentIf.append(self._ifCount)
            self._ifCount += 1
            self._ifNeedsCurlyBrace = False

        elif self._elseNeedsCurlyBrace:
            self._openCurlyBrace.append(['else', self._elseCount])
            self._elseNeedsCurlyBrace = False

        elif self._forLoopNeedsCurlyBrace:
            self._openCurlyBrace.append(['for', self._forLoopCount])
            self._currentForLoop.append(self._forLoopCount)
            self._forLoopCount += 1
            self._forLoopNeedsCurlyBrace = False

        elif self._procedureNeedsCurlyBrace:
            self._openCurlyBrace.append('procedure')
            self._procedureNeedsCurlyBrace = False


        
    def NewErrorsFound(self): #Boolean
        if len(self._errorMessages) < self._errorCount:
            return True
        else:
            return False

    def ParameterCountMatch(self, procedureName, variableParameterList):
        for procedure in self._procedures:
            if procedure[0] == procedureName:
                if len(procedure[1]) == len(variableParameterList):
                    return True
        return False

    def ParameterTypeMatch(self, procedureName, variableParameterList):
        for procedure in self._procedures:
            if procedure[0] == procedureName:
                originalVariableList = procedure[1]
                for i in range(0, len(originalVariableList)):
                    if self.GetVariableType(variableParameterList[i][1]) == originalVariableList[i][1]:
                        return True
        return False
    
    # def PerformArrayParameterCheck(self, parameters, array):


    def PerformVariableCheck(self, variableName): #Checks for valid syntax, checks if the variable does not exist and checks if the variable has a value or not
        if not self.HasValidVariableSyntax(variableName):
            self._errorCount += 1
            errorMessage = 'Syntax error on line ' + str(self._lineNumber) + '. The variable "' + variableName + '" has invalid syntax.'
            self._errorMessages.append([self._lineNumber, errorMessage])
        
        elif not self.VariableNameExists(variableName):
            self._errorCount += 1
            errorMessage = 'Error on line ' + str(self._lineNumber) + '. The variable "' + variableName + '" is undefined.'
            self._errorMessages.append([self._lineNumber, errorMessage])
        
        elif not self.VariableHasValue(variableName):
            self._errorCount += 1
            errorMessage = 'Error on line ' + str(self._lineNumber) + '. The variable "' + variableName + '" has no value.'
            self._errorMessages.append([self._lineNumber, errorMessage])
    
    def PerformNewVariableCheck(self, variableName): #Checks for valid syntax and if the variable already exists
        if not self.HasValidVariableSyntax(variableName):
            self._errorCount += 1
            errorMessage = 'Syntax error on line ' + str(self._lineNumber) + '. The variable "' + variableName + '" has invalid syntax.'
            self._errorMessages.append([self._lineNumber, errorMessage])
        
        elif self.VariableNameExists(variableName):
            self._errorCount += 1
            errorMessage = 'Error on line ' + str(self._lineNumber) + '. The variable "' + variableName + '" is already defined.'
            self._errorMessages.append([self._lineNumber, errorMessage])

    def PerformAssignmentVariableCheck(self, variableName): #Checks for valid syntax, checks if the variable does not exist
        if not self.HasValidVariableSyntax(variableName):
            self._errorCount += 1
            errorMessage = 'Syntax error on line ' + str(self._lineNumber) + '. The variable "' + variableName + '" has invalid syntax.'
            self._errorMessages.append([self._lineNumber, errorMessage])
        
        elif not self.VariableNameExists(variableName):
            self._errorCount += 1
            errorMessage = 'Error on line ' + str(self._lineNumber) + '. The variable "' + variableName + '" is undefined.'
            self._errorMessages.append([self._lineNumber, errorMessage])

    def ProcedureExists(self, procedureName):

        #self._procedures.append([procedureName, variableParameterList])
        for procedure in self._procedures:
            if procedure[0] == procedureName:
                return True

        return False
    
    def ProcessArrayAssignmentStatement(self, statement):
        # <ARRAY ASSIGNMENT STATEMENT> ::= <VARIABLE NAME>[<EXP><ARRAY ASSIGNMENT LIST>
        # <ARRAY ASSIGNMENT LIST> ::= ,<EXP><ARRAY ASSIGNMENT LIST> | ] = <EXP>;

        arrayName = ''
        itemExpression = ''
        expression = ''
        arrayList =  []
        openBrackets = False
        closeBrackets = False
        semiColonFound = False

        for i in range(0,len(statement)):

            if statement[i] == ';':
                semiColonFound = True

                result = self.ProcessExpression(expression + ';', arrayName)
                #Could implement arrays to be allowed when using constant propagation
                array = self.GetArray(arrayName)
                delta = array[3]

                for j in range(len(arrayList)):
                    if j == 0:
                        self._operations.append(['clearRegister'])
                        
                    if self.VariableNameExists(arrayList[j]):
                        self._operations.append(['arrayOffsetVariable', delta[j], arrayList[j]])
                    else:
                        self._operations.append(['arrayOffset', delta[j], arrayList[j]])
                
                if self.VariableNameExists(result):
                    self._operations.append(['allocateValueFromVariableToArray', array[4], 4, array[1], result])
                else: 
                    self._operations.append(['allocateToArray', array[4], 4, array[1], result])


            elif closeBrackets:
                if statement[i] == ' ' and expression == '':
                    continue
                elif statement[i] == '=':
                    continue
                else:
                    expression += statement[i]
                    continue

            elif statement[i] == ']' and openBrackets:
                closeBrackets = True
                if itemExpression != '':
                    result = self.ProcessExpression(itemExpression + ';', arrayName)
                    #Could implement the arrays to be used in constant propagation. Will move on though for now.
                    arrayList.append(result)
                continue

            elif openBrackets and not closeBrackets:
                if statement[i] == ',':
                    result = self.ProcessExpression(itemExpression + ';', arrayName)
                    #Could implement the arrays to be used in constant propagation. Will move on though for now.
                    arrayList.append(result)
                    itemExpression = ''
                elif statement[i] == ' ' and itemExpression == '':
                    continue
                else:
                    itemExpression += statement[i]
                continue

            elif statement[i] == '[' and arrayName != '':
                openBrackets = True
                continue
            elif statement[i] == ' ':
                continue
            else:
                arrayName += statement[i]
        
        if not closeBrackets:
            self._errorCount += 1
            errorMessage = 'Error on line ' + str(self._lineNumber) + '. Missing closing bracket.'
            self._errorMessages.append([self._lineNumber, errorMessage])
        
        if not semiColonFound:
            self._errorCount += 1
            errorMessage = 'Error on line ' + str(self._lineNumber) + '. No semi-colon found after statement.'
            self._errorMessages.append([self._lineNumber, errorMessage])
        
            

            

    def ProcessArrayStatement(self, statement):
        # <ARRAY STATEMENT> ::= ARRAY <VARIABLE NAME>[<POS OR NEG>..<POS OR NEG><ARRAY LIST>
        # <POS OR NEG> ::= <NUMBER> | <NEGATIVE NUMBER>
        # <ARRAY LIST> ::= ,<POS OR NEG>..<POS OR NEG><ARRAY LIST> | ];
        arrayName = ''
        item = ''
        arrayList =  []
        openBrackets = False
        closeBrackets = False
        semiColonFound = False
        

        for i in range(0, len(statement)):

            if statement[i] == ';':
                semiColonFound = True
                continue

            if statement[i] == ']' and openBrackets:
                closeBrackets = True
                if item != '':
                    arrayList.append(item)
                    item = ''
                
                continue

            if openBrackets and not closeBrackets:
                if statement[i] == ',':
                    arrayList.append(item)
                    item = ''
                elif statement[i] == ' ' and item == '':
                    continue
                else:
                    item += statement[i]
                continue

            if statement[i] == '[' and arrayName != '':  
                openBrackets = True
                continue

            else:
                arrayName += statement[i]
        
        if closeBrackets:
            if semiColonFound:

                k = []
                delta = []
                lb = []
                lowerBound = 0
                arraySize = 1

                for item in arrayList:

                    item = item.replace('..', ' ')
                    varOne = item[0:item.find(' ')]
                    lb.append(int(varOne))
                    varTwo = item[item.find(' ') + 1: len(item)]

                    if (self.IsNumber(varOne) or self.IsNegativeNumber(varOne)) and (self.IsNumber(varTwo) or self.IsNegativeNumber(varTwo)):
                        value = int(varTwo) - int(varOne) + 1
                        k.append(value)
                        arraySize = arraySize * value

                    else:
                        self._errorCount += 1
                        errorMessage = 'Error on line ' + str(self._lineNumber) + '. Invalid parameters in array declaration'
                        self._errorMessages.append([self._lineNumber, errorMessage])
                    

                for i in range(1, len(k) + 1):
                    if i == len(k):
                        delta.append(1)
                        continue
                    
                    temp = 1
                    for j in range(i, len(k)):
                        temp = temp * k[j]
                    
                    delta.append(temp)
                
                for i in range(0, len(delta)):
                    lowerBound = lowerBound + lb[i]*delta[i]

                arrayVariableName = '_arr_' + str(self._arrayCount) + '_' + arrayName
                self._arrayCount += 1
                valueToAdd = ['num_array', arrayVariableName, arraySize, delta, lowerBound]
                self._uninitializedValues.append(valueToAdd)

            else:
                self._errorCount += 1
                errorMessage = 'Error on line ' + str(self._lineNumber) + '. No semi-colon found after array statement.'
                self._errorMessages.append([self._lineNumber, errorMessage])
        else:
            self._errorCount += 1
            errorMessage = 'Error on line ' + str(self._lineNumber) + '. Missing closing bracket in array declaration.'
            self._errorMessages.append([self._lineNumber, errorMessage])
            

    def ProcessAssignment(self, variableName, statement):
        # <NUM ASSIGNMENT STATEMENT> ::= <VARIABLE NAME> = <EXP>;
        # <FLOAT ASSIGNMENT STATEMENT> ::= <VARIABLE NAME> = <EXP>;
        # <STRING ASSIGNMENT STATEMENT> ::= <VARIABLE NAME> = <DEATH STAR>
        # <DEATH STAR> ::= <VARIABLE NAME><ALDERAAN> | <STRING CONSTANT>;
        # <STRING CONSTANT> ::= "<WORD>"
        # <ALDERAAN> ::= ; | + <VARIABLE NAME>;
        # <STRING CONCATENATION> ::= <VARIABLE NAME> = <VARIABLE NAME> + <VARIABLE NAME>;


        expression = ''
        fillExpression = False
        semicolonFound = False

        self.PerformAssignmentVariableCheck(variableName)
        variable = self.GetVariableName(variableName)
        variableType = self.GetVariableType(variable)

        for i in range (0, len(statement)):
            
            if statement[i] == ';':
                semicolonFound = True
                if variableType == 'num' or variableType == 'numPointer':
                    # <NUM ASSIGNMENT STATEMENT> ::= <VARIABLE NAME> = <EXP>;
                    result =  self.ProcessExpression(expression + ';', variable)
                    self.SetVariableHasValue(variable)
                    self.AddOrUpdateVariableValue(variable, result)
                    if self.IsNumber(result) or self.IsNegativeNumber(result):
                        self._operations.append(['numVariableAssignment', result, '', variable])
                
                elif variableType == 'float':
                    # <FLOAT ASSIGNMENT STATEMENT> ::= <VARIABLE NAME> = <EXP>;
                    result =  self.ProcessExpression(expression + ';', '')
                    self.SetVariableHasValue(variable)
                    self.AddOrUpdateVariableValue(variable, result)
                    self._operations.append(['floatVariableAssignment', result, '', variable])

                elif variableType == 'string':
                    # expression = stringConstant | variableName | variableName + variableName
                    self.SetVariableHasValue(variable)
                    self.ProcessStringAssignmentOrConcatenation(variable, expression + statement[i])

            elif statement[i] == '=':
                fillExpression = True
            
            elif expression == '' and statement[i] == ' ':
                continue
            
            elif fillExpression:
                expression += statement[i]
        
        if not semicolonFound:
            self._errorCount += 1
            errorMessage = 'Syntax error on line ' + str(self._lineNumber) + '. Missing semi-colon at end of statement.'
            self._errorMessages.append([self._lineNumber, errorMessage])

    def ProcessCaseStatement(self, statement):
        # SWITCH (<VARIABLE NAME>) { <CASE PART> }
        # statement = (<VARIABLE NAME>) | (<VARIABLE NAME>) { <CASE PART> }

        variableName = ''
        openParenCheck = False # When this is true we can 
        closeParenCheck = False # When this is true we can move on the body of the switch
        casePart = ''

        for i in range(0, len(statement)):

            if statement[i] == '(' and not openParenCheck:
                openParenCheck = True
            
            elif statement[i] == ')' and not closeParenCheck:

                closeParenCheck = True

                #Error Messages
                if not openParenCheck: # No opening parentheses
                    self._errorCount += 1
                    errorMessage = 'Error on line ' + str(self._lineNumber) + '. No opening parentheses for switch statement.'
                    self._errorMessages.append([self._lineNumber, errorMessage])
                elif variableName == '': # No variable name
                    self._errorCount += 1
                    errorMessage = 'Error on line ' + str(self._lineNumber) + '. No variable supplied to switch statement.'
                    self._errorMessages.append([self._lineNumber, errorMessage])
                elif not self.VariableNameExists(variableName): # Variable indicated does not exist
                    self._errorCount += 1
                    errorMessage = 'Error on line ' + str(self._lineNumber) + '. The variable \"' + variableName + '\" is undefined.'
                    self._errorMessages.append([self._lineNumber, errorMessage])
                elif not self.VariableHasValue(variableName): # Variable does not have a value
                    self._errorCount += 1
                    errorMessage = 'Error on line ' + str(self._lineNumber) + '. The variable \"' + variableName + '\" has no value.'
                    self._errorMessages.append([self._lineNumber, errorMessage])
                else:
                    assemblyVariableName = self.GetVariableName(variableName)
                    self._switchVariable.append(assemblyVariableName)
                    self._operations.append(['switch', assemblyVariableName])

                self._switchNeedsCurlyBrace = True
            
            elif openParenCheck and not closeParenCheck: # all characters within this range are what is held in the variable name
                if statement[i] == ' ':
                    continue
                variableName += statement[i]

            elif openParenCheck and closeParenCheck:
                # { <CASE PART> } check for this
                if statement[i] == '{':
                    self.NewCurlyBraceFound()
                
                elif statement[i] == '}':
                    self.ProcessCasePart(casePart)
                    self.CloseCurlyBrace()
                
                else:
                    casePart += statement[i]


    def ProcessCasePart(self, casePart):
        # CASE <EXP>:{<STATEMENT>} <CASE PART> | DEFAULT:{<STATEMENT>}

        caseExpressionResult = ''
        expression = ''
        keyword = ''
        statement = ''
        newCasePart = ''
        keywordFound = False
        caseTypeFound = False
        statementFound = False

        for i in range(0, len(casePart)):
            
            if not caseTypeFound:
                if casePart[i] == ':': # CASE <EXP>: | DEFAULT:
                    caseTypeFound = True

                    if keyword == 'default':
                        self._defaultCaseNeedsCurlyBrace = True

                    elif keyword == 'case':
                        self._caseNeedsCurlyBrace = True
                        caseExpressionResult = self.ProcessExpression(expression + ';', '')

                        # Need to add operation here for assembly
                        #Case is a jump where we compare the contents of what is held in the switch
                        self._operations.append(['case', self._caseCount, caseExpressionResult])
                    
                    else: #Error invalid syntax
                        self._errorCount += 1
                        errorMessage = 'Syntax error on line ' + str(self._lineNumber) + '. Missing "case" or "default" keyword in statement.'
                        self._errorMessages.append([self._lineNumber, errorMessage])

                elif casePart[i] == ' ':
                    if keyword == '':
                        continue
                    else:
                        keywordFound = True

                elif keywordFound:
                    expression += casePart[i]

                else:
                    keyword += casePart[i]
            
            else:
                # {<STATEMENT>} <CASE PART> | {<STATEMENT>}
                if casePart[i] == '{':
                    self.NewCurlyBraceFound()
                
                elif casePart[i] == '}':
                    statementFound = True
                    self.ProcessStatement(statement)
                    self.CloseCurlyBrace() # In this method need to add an operation that will produce the closing code for the specific portion of code included there.

                elif not statementFound:
                    statement += casePart[i]
                
                else:
                    newCasePart += casePart[i]

        if newCasePart == '':
            return
        else:
            self.ProcessCasePart(newCasePart)

    def ProcessElseStatement(self):
        self._elseNeedsCurlyBrace = True
        ifOperation = self._operations[len(self._operations) - 1]
        self._operations.pop()
        elseOperation = ['elseBegin', self._elseCount]
        self._operations.append(elseOperation)
        self._operations.append(ifOperation)


    def ProcessExpression(self, expression, variableName):
        prefixExpression = self.FindPrefixExpression(expression)
        return self.ProcessPrefixExpression(prefixExpression, variableName)
    
    def ProcessFloatDeclarationStatement(self, statement):
        # statement = <VARIABLE NAME><DELTA>
            #<DELTA> ::= ; | = <EXP>;
        variableName = ''
        expression = ''
        variableNameFound = False
        semicolonFound = False

        for i in range(0, len(statement)):
            
            if statement[i] == ';' and expression == '':
                semicolonFound = True
                #Add the variable to the uninitialized list
                if not self.HasValidVariableSyntax(variableName):
                    self._errorCount += 1
                    errorMessage = 'Syntax error on line ' + str(self._lineNumber) + '. Variable name contains invalid characters.\n'
                    self._errorMessages.append([self._lineNumber, errorMessage])
                elif self.VariableNameExists(variableName):
                    self._errorCount += 1
                    errorMessage = 'Error on line ' + str(self._lineNumber) + '. Program already contains definition of variable name \"' + variableName + '\".\n'
                    self._errorMessages.append([self._lineNumber, errorMessage])
                else:
                    self._uninitializedValues.append(['float', '_f_' + str(self._varNumCount) + '_' + variableName, 'no value'])
                    self._varNumCount += 1
            
            elif statement[i] == ';' and expression != '':
                semicolonFound = True
                if not self.HasValidVariableSyntax(variableName):
                    self._errorCount += 1
                    errorMessage = 'Syntax error on line ' + str(self._lineNumber) + '. Variable name contains invalid characters.\n'
                    self._errorMessages.append([self._lineNumber, errorMessage])
                else:
                    #Process the expression
                    result = self.ProcessExpression(expression + statement[i], variableName)
                    self.AddOrUpdateVariableValue(self.GetVariableName(variableName), result)
                    if self.IsFloatingPointNumber(result) or self.IsNegativeFloatingPointNumber(result):
                        self._uninitializedValues.append(['float', '_f_' + str(self._varFloatCount) + '_' + variableName, 'Has value'])
                        self._operations.append(['floatVariableAssignment', result, '', self.GetVariableName(variableName)])
                    else:
                        self._uninitializedValues.append(['float', '_f_' + str(self._varFloatCount) + '_' + variableName, 'Has value'])
                        self._operations.append(['floatVariableAssignment', result, '', self.GetVariableName(variableName)])

                    self._varFloatCount += 1

            elif (statement[i] == ' ' or statement[i] == '=') and not variableNameFound:
                variableNameFound = True
            
            elif statement[i] == '=':
                continue
            
            elif variableNameFound:
                if statement[i] == ' ' and expression == '':
                    continue
                expression += statement[i]

            elif not variableNameFound:
                variableName += statement[i]
        
        if not semicolonFound:
            self._errorCount += 1
            errorMessage = 'Syntax error on line ' + str(self._lineNumber) + '. Missing semi-colon at end of statement.'
            self._errorMessages.append([self._lineNumber, errorMessage])


        
    
    def ProcessForStatement(self, statement):
        # statement = <VARIABLE NAME> = <EXP> TO <EXP> STEP <EXP> DO { <STATEMENT> }
        variableName = ''
        varExpression = ''
        toExpression = ''
        stepExpression = ''
        variableNameFound = False
        varFound = False
        toFound = False
        stepFound = False
        forLoopParameters = []

        forLoopParameters.append(self._forLoopCount)

        self._forLoopNeedsCurlyBrace = True

        for i in range(0, len(statement)):
            
            if stepFound:
                if statement[i] == '{':
                    self.NewCurlyBraceFound()
                    return self.ProcessStatement(statement[i + 1: len(statement)])
            
            if toFound and not stepFound:
                if stepExpression == '' and statement[i] == ' ':
                    continue
                elif (stepExpression != '' and statement[i] == ' ') or statement[i] != ' ':
                    if (statement[i - 1].lower() == 'o' and statement[i - 2].lower() == 'd' and statement[i - 3] == ' ') or (statement[i].lower() == 'o' and statement[i - 1].lower() == 'd' and statement[i - 2] == ' '):
                        stepFound = True
                        index = 2
                        if statement[i].lower() == ' ':
                            index = 3
                        stepExpression = stepExpression[0: len(stepExpression) - index]
                        stringStep = '_n_' + str(self._varNumCount) + '_step_' + str(self._forStepCount)
                        self._uninitializedValues.append(['num', stringStep, 'Has value'])
                        result = self.ProcessExpression(stepExpression + ';', stringStep)
                        self.AddOrUpdateVariableValue(stringStep, result)
                        if self.IsNumber(result) or self.IsNegativeNumber(result):
                            self._operations.append(['numVariableAssignment', result, '', stringStep])
                        forLoopParameters.append(stringStep)
                        self._varNumCount += 1
                        self._forStepCount += 1

                        # Add begin for loop operation
                        self._forLoopParametersStack.append(forLoopParameters)
                        self._operations.append(['beginForLoop', forLoopParameters[0], forLoopParameters[1], forLoopParameters[2]])
                    else:
                        stepExpression += statement[i]
            
            if varFound and not toFound:

                if toExpression == '' and statement[i] == ' ':
                    continue
                elif (toExpression != '' and statement[i] == ' ') or statement[i] != ' ':
                    if statement[i - 1].lower() == 'p' and statement[i - 2].lower() == 'e' and statement[i - 3].lower() == 't' and statement[i - 4].lower() == 's' and statement[i - 5] == ' ':
                        toFound = True
                        toExpression = toExpression[0: len(toExpression) - 5]
                        stringTo = '_n_' + str(self._varNumCount) + '_to_' + str(self._forToCount)
                        self._uninitializedValues.append(['num', stringTo, 'Has value'])
                        result = self.ProcessExpression(toExpression + ';', stringTo)
                        self.AddOrUpdateVariableValue(stringTo, result)
                        if self.IsNumber(result) or self.IsNegativeNumber(result):
                            self._operations.append(['numVariableAssignment', result, '', stringTo])
                        forLoopParameters.append(stringTo)
                        self._varNumCount += 1
                        self._forToCount += 1
                    else:
                        toExpression += statement[i]

            if variableNameFound and not varFound:

                if varExpression == '' and statement[i] == ' ':
                    continue
                elif (varExpression != '' and statement[i] == ' ') or statement[i] != ' ':
                    if statement[i - 1].lower() == 'o' and statement[i - 2].lower() == 't' and statement[i - 3] == ' ':
                        varFound = True
                        varExpression = varExpression[0: len(varExpression) - 3]
                        result = self.ProcessExpression(varExpression + ';', self.GetVariableName(variableName))
                        self.AddOrUpdateVariableValue(self.GetVariableName(variableName), result)
                        if self.IsNumber(result) or self.IsNegativeNumber(result):
                            self._operations.append(['numVariableAssignment', result, '', self.GetVariableName(variableName)])
                        forLoopParameters.append(self.GetVariableName(variableName))
                    else:
                        varExpression += statement[i]
            
            if statement[i] == '=':
                if variableName[len(variableName) - 1] == ' ':
                    variableName = variableName[0:len(variableName) - 1]
                
                self.PerformAssignmentVariableCheck(variableName)
                self.SetVariableHasValue(variableName)
                variableNameFound = True

            if not variableNameFound:
                variableName += statement[i]

    def ProcessIfStatement(self, statement):
        # statement = <CONDITION> THEN { <STATEMENT>} <THE FORCE>
        # <THE FORCE> ::= e | ELSE { <STATEMENT> }

        leftHandExpression = ''
        rightHandExpression = ''
        relationalOperator = ''
        tempExpression = ''
        ifStatementComplete = False
        openParenthesesCount = 0

        for i in range(0, len(statement)):
            # First (<NUMBER> | <NEGATIVE NUMBER> | <VARIABLE NAME><REF>) or it can even be it's own expression within parentheses
            # It can be a number, a negative number or a variable or an array reference
            if statement[i] == ' ' and openParenthesesCount == 0 and not ifStatementComplete:
                if leftHandExpression == '':
                    leftHandExpression = tempExpression
                    tempExpression = ''
                elif relationalOperator == '':
                    relationalOperator = tempExpression
                    tempExpression = ''
                elif rightHandExpression == '':
                    rightHandExpression = tempExpression
                    tempExpression = ''
            
            if statement[i] == ' ':
                continue
            else:
                if statement[i] == '(':
                    openParenthesesCount += 1
                elif statement[i] == ')':
                    if openParenthesesCount == 0:
                        self._errorCount += 1
                        errorMessage = 'Syntax error on line ' + str(self._lineNumber) + '. Missing opening Parentheses.\n'
                        self._errorMessages.append([self._lineNumber, errorMessage])
                    else:
                        openParenthesesCount -= 1
                elif statement[i] == '{' and ifStatementComplete:
                    self.NewCurlyBraceFound()
                    return self.ProcessStatement(statement[i + 1: len(statement)])

                tempExpression += statement[i]
            
            if leftHandExpression != '' and relationalOperator != '' and rightHandExpression != '' and tempExpression.lower() == 'then':
                ifStatementComplete = True
                self._ifNeedsCurlyBrace = True
                left = self.ProcessExpression(leftHandExpression + ';', '')
                right = self.ProcessExpression(rightHandExpression + ';', '')
                self._operations.append(['beginIfStatement', self._ifCount, left, right, relationalOperator])



    def ProcessNumDeclarationStatement(self, statement):
        #statement  = <VARIABLE NAME><DELTA>
            #<DELTA> ::= ; | = <EXP>;
        variableName = ''
        expression = ''
        variableNameFound = False
        semicolonFound = False

        for i in range(0, len(statement)):
            
            if statement[i] == ';' and expression == '':
                semicolonFound = True
                #Add the variable to the uninitialized list
                if not self.HasValidVariableSyntax(variableName):
                    self._errorCount += 1
                    errorMessage = 'Syntax error on line ' + str(self._lineNumber) + '. Variable name contains invalid characters.\n'
                    self._errorMessages.append([self._lineNumber, errorMessage])
                elif self.VariableNameExists(variableName):
                    self._errorCount += 1
                    errorMessage = 'Error on line ' + str(self._lineNumber) + '. Program already contains definition of variable name \"' + variableName + '\".\n'
                    self._errorMessages.append([self._lineNumber, errorMessage])
                else:
                    self._uninitializedValues.append(['num', '_n_' + str(self._varNumCount) + '_' + variableName, 'no value'])
                    self._varNumCount += 1
            
            elif statement[i] == ';' and expression != '':
                semicolonFound = True
                if not self.HasValidVariableSyntax(variableName):
                    self._errorCount += 1
                    errorMessage = 'Syntax error on line ' + str(self._lineNumber) + '. Variable name contains invalid characters.\n'
                    self._errorMessages.append([self._lineNumber, errorMessage])
                else:
                    #Process the expression
                    result = self.ProcessExpression(expression + statement[i], variableName)
                    self.AddOrUpdateVariableValue('_n_' + str(self._varNumCount) + '_' + variableName, result)
                    if self.IsNumber(result) or self.IsNegativeNumber(result):
                        self._initializedValues.append(['num', '_n_' + str(self._varNumCount) + '_' + variableName, result])
                    else:
                        self._uninitializedValues.append(['num', '_n_' + str(self._varNumCount) + '_' + variableName, 'Has value'])
                        self._operations.append(['numVariableAssignment', result, '', self.GetVariableName(variableName)])
                    self._varNumCount += 1

            elif (statement[i] == ' ' or statement[i] == '=') and not variableNameFound:
                variableNameFound = True
            
            elif statement[i] == '=':
                continue
            
            elif variableNameFound:
                expression += statement[i]

            elif not variableNameFound:
                variableName += statement[i]
        
        if not semicolonFound:
            self._errorCount += 1
            errorMessage = 'Syntax error on line ' + str(self._lineNumber) + '. Missing semi-colon at end of statement.'
            self._errorMessages.append([self._lineNumber, errorMessage])
                  

    def ProcessPrefixExpression(self, prefixExpression, variableName):
        #returns the variable holding the result of the expression

        processComplete = False

        expression = prefixExpression
        tempVariableCount = 0
        returnResult = ''
        isBaseTwo = False
        negativeBitShift = False

        if self._uselessCodeRemoval:
            expression = self.UselessCodeRemoval(expression)

        if self._constantPropagation:
            expression = self.ConstantPropagation(expression)

        if self._constantFolding:
            expression = self.ConstantFolding(expression)

        expressionWithoutEndingSpace = expression[0:len(expression) - 1]

        if self.IsNumber(expressionWithoutEndingSpace) or self.IsNegativeNumber(expressionWithoutEndingSpace) or self.IsFloatingPointNumber(expressionWithoutEndingSpace) or self.IsNegativeFloatingPointNumber(expressionWithoutEndingSpace):
            return expressionWithoutEndingSpace
        
        if expressionWithoutEndingSpace.find(' ') == -1: # single variable assignment
            self.PerformVariableCheck(expressionWithoutEndingSpace)
            tempOperand1 = self.GetVariableName(expressionWithoutEndingSpace)
            result = self.GetVariableName(variableName)
            operandType = self.GetVariableType(expressionWithoutEndingSpace)
            if operandType == 'num':
                if result == None or result == '' or result.find('_arr_') == -1:
                    if result != None and result != '':
                        self._operations.append(['numVariableAssignment', tempOperand1, '', result])
                    elif variableName != '':
                        self._operations.append(['numVariableAssignment', tempOperand1, '', '_n_' + str(self._varNumCount) + '_' + variableName])
                    return tempOperand1
                else:
                    return tempOperand1
            elif operandType == 'float':
                if result == None or result == '' or result.find('_arr_') == -1:
                    if result != None and result != '':
                        self._operations.append(['floatVariableAssignment', tempOperand1, '', result])
                    else:
                        self._operations.append(['floatVariableAssignment', tempOperand1, '', '_f_' + str(self._varFloatCount) + '_' + variableName])
                    return tempOperand1
                else:
                    return tempOperand1

        while not processComplete:
            
            index = 0
            operator = ''
            result = ''
            tempOperatorIndex = 0
            tempOperator = ''
            tempOperand1 = ''
            tempOperand2 = ''
            tempVariable = ''
            

            for char in expression:
                
                if char == ' ':
                    index += 1
                    continue
                else:
                    if self.IsOperator(char) or tempVariable == '':
                        tempVariable = char
                    else:
                        tempVariable = tempVariable + char

                if expression[index + 1] == ' ' and not self.IsOperator(tempVariable):
                    if self.IsNumber(tempVariable) or self.VariableHasValue(tempVariable) or self.IsNegativeNumber(tempVariable) or self.IsFloatingPointNumber(tempVariable) or self.IsNegativeFloatingPointNumber(tempVariable):
                        if tempOperand1 == '':
                            if self.VariableHasValue(tempVariable):
                                tempOperand1 = self.GetVariableName(tempVariable)
                            else:
                                tempOperand1 = tempVariable
                            tempVariable = ''
                        elif index - 1 != tempOperatorIndex:
                            if self.VariableHasValue(tempVariable):
                                tempOperand2 = self.GetVariableName(tempVariable)
                            else:
                                tempOperand2 = tempVariable
                elif self.IsOperator(tempVariable) and not self.IsNegativeNumberIndex(index):
                    tempOperator = tempVariable
                    tempOperatorIndex = index
                    tempVariable = ''
                    tempOperand1 = ''
                
                if tempOperand2 != '':
                    break
                else:
                    index += 1

            if (self.IsNumber(tempOperand1) or self.IsNegativeNumber(tempOperand1) or self.GetVariableType(tempOperand1) == 'num') and (self.IsNumber(tempOperand2) or self.IsNegativeNumber(tempOperand2) or self.GetVariableType(tempOperand2) == 'num'):
                
                if self._multiplyOrDivideBy2 and tempOperator == '*':

                    # TempOperand1
                    if self.IsNumber(tempOperand1):
                        isBaseTwo = math.log(int(tempOperand1),2).is_integer()
                        if isBaseTwo:
                            tempOperand1 = str(int(math.log(int(tempOperand1),2)))

                    elif self.IsNegativeNumber(tempOperand1):
                        isBaseTwo = math.log(int(tempOperand1[1:len(tempOperand1)]),2).is_integer()
                        if isBaseTwo:
                            tempOperand1 = str(int(math.log(int(tempOperand1[1:len(tempOperand1)]),2)))
                            if self.IsNumber(tempOperand2):
                                tempOperand2 = '-' + tempOperand2
                            elif self.IsNegativeNumber(tempOperand2):
                                tempOperand2 = tempOperand2[1:len(tempOperand2)]
                            elif self.VariableHasValue(tempOperand2):
                                negativeBitShift = True
                    # elif self.VariableHasValue(tempOperand1):
                    #     isBaseTwo = math.log(int(self.GetVariableValue(tempOperand1)),2).is_integer()
                    #     if isBaseTwo:
                    #         tempOperand1 = str(int(math.log(int(self.GetVariableValue(tempOperand1)),2)))
                    
                    # TempOperand2
                    if not isBaseTwo and self.IsNumber(tempOperand2):
                        isBaseTwo = math.log(int(tempOperand2),2).is_integer()
                        if isBaseTwo:
                            a = tempOperand1
                            tempOperand1 = str(int(math.log(int(tempOperand2),2)))
                            tempOperand2 = a
                    
                    elif not isBaseTwo and self.IsNegativeNumber(tempOperand2):
                        isBaseTwo = math.log(int(tempOperand2[1:len(tempOperand2)]),2).is_integer()
                        if isBaseTwo:
                            a = tempOperand1
                            tempOperand1 = str(int(math.log(int(tempOperand2[1:len(tempOperand2)]),2)))
                            tempOperand2 = a
                            if self.IsNumber(tempOperand2):
                                tempOperand2 = '-' + tempOperand2
                            elif self.IsNegativeNumber(tempOperand2):
                                tempOperand2 = tempOperand2[1:len(tempOperand2)]
                            elif self.VariableHasValue(tempOperand2):
                                negativeBitShift = True

                    # elif not isBaseTwo and self.VariableHasValue(tempOperand2):
                    #     isBaseTwo = math.log(int(self.GetVariableValue(tempOperand2)),2).is_integer()
                    #     if isBaseTwo:
                    #         a = tempOperand1
                    #         tempOperand1 = str(int(math.log(int(self.GetVariableValue(tempOperand2)),2)))
                    #         tempOperand2 = a
                    #         if self.IsNumber(tempOperand1):
                    #             tempOperand1 = '-' + tempOperand1
                    #         elif self.IsNegativeNumber(tempOperand1):
                    #             tempOperand1 = tempOperand1[1:len(tempOperand1)]
                
                if self._operatorCount <= 1:

                    if self._operatorCount == 0:
                        operator = 'numVariableAssignment'

                    result = self.GetVariableName(variableName)
                    
                    if result == '' or result == None or result.find('_arr_') != -1:
                        
                        result = '_n_' + str(self._varNumCount) + '_t' + str(tempVariableCount)
                        tempVariable = 't' + str(tempVariableCount)

                        if not self.VariableNameExists('t' + str(tempVariableCount)) or self.GetVariableType('t' + str(tempVariableCount)) != 'num':
                            if self.VariableNameExists('t' + str(tempVariableCount)):
                                tempVariableCount += 1
                            result = '_n_' + str(self._varNumCount) + '_t' + str(tempVariableCount)
                            self._uninitializedValues.append(['num', result, 'Has value'])
                            self._tempVariables.append('t' + str(tempVariableCount))
                            tempVariableCount += 1
                            self._varNumCount += 1
                        else:
                            result = self.GetVariableName('t' + str(tempVariableCount))
                            tempVariableCount += 1

                else:
                    if index + 1 > len(expression) and tempOperand2 == '' and tempOperand1 != '':
                        return tempOperand1

                    result = '_n_' + str(self._varNumCount) + '_t' + str(tempVariableCount)
                    tempVariable = 't' + str(tempVariableCount)

                    if not self.VariableNameExists('t' + str(tempVariableCount)) or self.GetVariableType('t' + str(tempVariableCount)) != 'num':
                        if self.VariableNameExists('t' + str(tempVariableCount)):
                            tempVariableCount += 1
                        result = '_n_' + str(self._varNumCount) + '_t' + str(tempVariableCount)
                        self._uninitializedValues.append(['num', result, 'Has value'])
                        self._tempVariables.append('t' + str(tempVariableCount))
                        tempVariableCount += 1
                        self._varNumCount += 1
                    else:
                        result = self.GetVariableName('t' + str(tempVariableCount))
                        tempVariableCount += 1
            else:
                if self._operatorCount <= 1:

                    if self._operatorCount == 0:
                        operator = 'floatVariableAssignment'

                    result = self.GetVariableName(variableName)
                    
                    if result == '' or result == None or result.find('_arr_') != -1:
                        
                        result = '_f_' + str(self._varFloatCount) + '_t' + str(tempVariableCount)
                        tempVariable = 't' + str(tempVariableCount)

                        if not self.VariableNameExists('t' + str(tempVariableCount)) or self.GetVariableType('t' + str(tempVariableCount)) != 'float':
                            if self.VariableNameExists('t' + str(tempVariableCount)):
                                tempVariableCount += 1
                            result = '_f_' + str(self._varFloatCount) + '_t' + str(tempVariableCount)
                            self._uninitializedValues.append(['float', result, 'Has value'])
                            self._tempVariables.append('t' + str(tempVariableCount))
                            tempVariableCount += 1
                            self._varFloatCount += 1
                        else:
                            result = self.GetVariableName('t' + str(tempVariableCount))
                            tempVariableCount += 1

                else:
                    if index + 1 > len(expression) and tempOperand2 == '' and tempOperand1 != '':
                        return tempOperand1

                    result = '_f_' + str(self._varFloatCount) + '_t' + str(tempVariableCount)
                    tempVariable = 't' + str(tempVariableCount)

                    if not self.VariableNameExists('t' + str(tempVariableCount)) or self.GetVariableType('t' + str(tempVariableCount)) != 'float':
                        if self.VariableNameExists('t' + str(tempVariableCount)):
                            tempVariableCount += 1
                        result = '_f_' + str(self._varFloatCount) + '_t' + str(tempVariableCount)
                        self._uninitializedValues.append(['float', result, 'Has value'])
                        self._tempVariables.append('t' + str(tempVariableCount))
                        tempVariableCount += 1
                        self._varFloatCount += 1
                    else:
                        result = self.GetVariableName('t' + str(tempVariableCount))
                        tempVariableCount += 1

            #Add the operation
            if tempOperator == '+':
                operator = 'add'
            elif tempOperator == '-':
                operator = 'subtract'
            elif tempOperator == '*' and isBaseTwo:
                if negativeBitShift:
                    operator = 'negativeBitShift'
                else:
                    operator = 'bitShift'
            elif tempOperator == '*':
                operator = 'multiply'
            elif tempOperator == '^':
                operator = 'exponentiate'

            if self.GetVariableType(tempOperand1) == 'float' or self.GetVariableType(tempOperand2) == 'float' or (self.IsFloatingPointNumber(tempOperand1) or self.IsNegativeFloatingPointNumber(tempOperand1)) or (self.IsFloatingPointNumber(tempOperand2) or self.IsNegativeFloatingPointNumber(tempOperand2)):
                self._operations.append([operator +'Float', tempOperand1, tempOperand2, result])
            else:
                self._operations.append([operator, tempOperand1, tempOperand2, result])
            self.SetVariableHasValue(result)


            # if(expression[0:tempOperatorIndex] != '' or expression[index:len(expression)] != ''):
            expression = expression[0:tempOperatorIndex] + tempVariable + expression[index + 1:len(expression)]
            self._operatorCount -= 1

            if self._operatorCount <= 0:
                self._operatorCount = 0
                returnResult = result
                processComplete = True
        
        return returnResult

    def ProcessProceduralCall(self, statement):
        # <PROCEDURE CALL STATEMENT> ::= <VARIABLE NAME> ( <VARIABLE PASS>

        procedureName = ''

        for i in range(0, len(statement)):

            if ((statement[i] == ' ' and statement[i + 1] == '(') or statement[i] == '('):
                
                if not self.HasValidVariableSyntax(procedureName): #Validate the procedure name has valid syntax
                    self._errorCount += 1
                    errorMessage = 'Syntax error on line ' + str(self._lineNumber) + '. The procedure name "' + procedureName + '" has invalid syntax.'
                    self._errorMessages.append([self._lineNumber, errorMessage])
                else:
                    # <VARIABLE PASS> ::= ); | <VARIABLES PASSED IN>

                    self.ProcessVariablePass(procedureName, statement[i + 1: len(statement)])
            else:
                procedureName += statement[i]

    def ProcessProcedureDeclarationStatement(self, statement):
        # statement = <VARIABLE NAME> ( <VARIABLE PASSING>

        procedureName = ''
        procedureNameFound = False

        for i in range(0, len(statement)):

            if (statement[i] == ' ' or statement[i] == '(') and not procedureNameFound:
                
                if not self.HasValidVariableSyntax(procedureName): #Validate the procedure name has valid syntax
                    self._errorCount += 1
                    errorMessage = 'Syntax error on line ' + str(self._lineNumber) + '. The procedure name "' + procedureName + '" has invalid syntax.'
                    self._errorMessages.append([self._lineNumber, errorMessage])
                else:
                    procedureNameFound = True
                
                if statement[i] == '(':
                    return self.ProcessVariablePassing(procedureName, statement[i + 1:len(statement)])
            elif procedureNameFound and statement[i] == '(':
                # <VARIABLE PASSING> ::= ) { <STATEMENT> } | <VARIABLE LIST>

                return self.ProcessVariablePassing(procedureName, statement[i + 1:len(statement)])
            
            elif not procedureNameFound:
                procedureName += statement[i]




    def ProcessProgramFile(self, programFile, fileName):
        
        statementWithoutComments = '' #string
        programVariableName = ''      #string

        for originalStatement in programFile.readlines():
            
            self._lineNumber += 1

            statementWithoutComments = self.RemoveCommentsFromStatement(originalStatement)

            if self.NewErrorsFound():
                errorMessage = statementWithoutComments
                self._errorMessages.append([self._lineNumber, errorMessage])
            
            strg = statementWithoutComments
            statement = ''

            for i in range(0, len(statementWithoutComments)):

                if strg[i] == '\t':
                    continue

                if statement.lower() == 'program':
                    if strg[i] != ';' and ((strg[i + 1] == ' ' and programVariableName != '') or (i + 1 == len(statementWithoutComments))):
                        self._errorCount += 1
                        errorMessage = 'Syntax error on line ' + str(self._lineNumber) + '. Missing semi-colon after program name.\n'
                        self._errorMessages.append([self._lineNumber, errorMessage])
                        statement = ''
                    
                    elif strg[i] == ';' and programVariableName != '':
                        if not self.HasValidVariableSyntax(programVariableName):
                            self._errorCount += 1
                            errorMessage = 'Syntax error on line ' + str(self._lineNumber) + '. Program name contains invalid characters.\n'
                            self._errorMessages.append([self._lineNumber, errorMessage])
                            statement = ''
                            continue
                        else:
                            statement = ''
                            self._programVariableName = programVariableName
                            continue
                    else:
                        if(strg[i] == ' ' and programVariableName == ''):
                            continue
                        programVariableName += strg[i]
                        continue
                
                elif self._programVariableName != '' and self._statementsValid == False:
                    if statement.lower() == 'begin':
                        if strg[i] == ' ' or strg[i] == '\n':
                            self._statementsValid = True
                            statement = ''
                            continue
                
                elif self._statementsValid == True:
                    if statement.lower() == 'end':
                        if (i + 1 == len(statementWithoutComments) or strg[i + 1] == ' '):
                            if strg[i] != '.':
                                self._errorCount += 1
                                errorMessage = 'Syntax error on line ' + str(self._lineNumber) + '. Expected period \".\" after end keyword'
                                self._errorMessages.append([self._lineNumber, errorMessage])
                            else: 
                                self._statementsValid = False
                                statement = '' 
                
                if strg[i] == '\n':
                    continue
                
                if strg[i] == ' ' and statement == '':
                    continue
                else:
                    statement += strg[i]

                

            #Process the statement
            if statement != '':
                if self._statementsValid: # and statement[len(statement) - 1: len(statement)] == ';' **** NOT ALL STATEMENTS NEED TO END WITH A SEMI-COLON TO BE VALID. IT DEPENDS ON WHAT KIND OF STATEMENT IT IS *****
                    self.ProcessStatement(statement)

                # elif not self._statementsValid:
                #     self._errorCount += 1
                #     errorMessage = 'Syntax error on line ' + str(self._lineNumber) + '.Missing semi-colon \";\" after statement.'
                #     self._errorMessages.append([self._lineNumber, errorMessage])

                # elif statement[len(statement) - 1: len(statement)] != ';' and statement != 'end.':
                #     self._errorCount += 1
                #     errorMessage = 'Syntax error on line ' + str(self._lineNumber) + '.Missing semi-colon \";\" after statement.'
                #     self._errorMessages.append([self._lineNumber, errorMessage])    

        if self._errorCount != 0:
            return self._errorMessages
        else:
            return [[0, 'valid']]

    def ProcessStatement(self, statement):
        
        #<STATEMENT> ::= <READ STATEMENT><STATEMENT> | <WRITE STATEMENT><STATEMENT> | <FOR STATEMENT><STATEMENT> | <IF STATEMENT><STATEMENT> | <CASE STATEMENT><STATEMENT> | <NUM ASSIGNMENT STATEMENT><STATEMENT> | <STRING ASSIGNMENT STATEMENT><STATEMENT> | <ARRAY STATEMENT><STATEMENT> | <PROCEDURE DECLARATION STATEMENT><STATEMENT> | <PROCEDURE CALL STATEMENT><STATEMENT> | <RETURN STATEMENT><STATEMENT> | <NUM DECLARATION STATEMENT><STATEMENT> | <STRING DECLARATION STATEMENT><STATEMENT> | <STRING CONCATENATION><STATEMENT> | <ARRAY ASSIGNMENT STATEMENT><STATEMENT> | e
        token = ''

        for i in range(0, len(statement)):
            
            #<NUM DECLARATION STATEMENT> ::= NUM <VARIABLE NAME><DELTA>
            if token == 'num' and statement[i] == ' ':
                return self.ProcessNumDeclarationStatement(statement[i + 1 : len(statement)]) # Needs a semi colon
            
            # <FLOAT DECLARATION STATEMENT> ::= FLOAT <VARIABLE NAME><DELTA>
            if token == 'float' and statement[i] == ' ':
                return self.ProcessFloatDeclarationStatement(statement[i + 1: len(statement)])

            # <STRING DECLARATION STATEMENT> ::= STRING <VARIABLE NAME><DARTH VADER>
            elif token == 'string' or token == 'String' and statement[i] == ' ':
                return self.ProcessStringDeclarationStatement(statement[i + 1 : len(statement)]) # Needs a semi colon
            

            # <ARRAY STATEMENT> ::= ARRAY <VARIABLE NAME>[<POS OR NEG>..<POS OR NEG><ARRAY LIST>
            elif token == 'array' and statement[i] == ' ':
                return self.ProcessArrayStatement(statement[i + 1 : len(statement)]) # Needs a semi colon

            # <READ STATEMENT> ::= READ <VARIABLE NAME>;
            elif token == 'read' and statement[i] == ' ':
                # return self.ProcessReadStatement(statement[i + 1 : len(statement)]) # Needs a semi colon
                pass


            # <PROCEDURE DECLARATION STATEMENT> ::= PROCEDURE <VARIABLE NAME> ( <VARIABLE PASSING>
            elif token == 'procedure' and statement[i] == ' ':
                return self.ProcessProcedureDeclarationStatement(statement[i + 1 : len(statement)])


            # <WRITE STATEMENT> ::= WRITE <ALPHA>
            elif token == 'write' and statement[i] == ' ':
                return self.ProcessWriteStatement(statement[i + 1 : len(statement)]) # Needs a semi colon
            

            # <FOR STATEMENT> ::= FOR <VARIABLE NAME> = <EXP> TO <EXP> STEP <EXP> DO { <STATEMENT> }
            elif token == 'for' and statement[i] == ' ':
                return self.ProcessForStatement(statement[i + 1 : len(statement)])


            # <IF STATEMENT> ::= IF <CONDITION> THEN { <STATEMENT>} <THE FORCE>
            elif token == 'if' and statement[i] == ' ':
                return self.ProcessIfStatement(statement[i + 1 : len(statement)])
            
            elif token == 'else' and statement[i] == ' ':
                return self.ProcessElseStatement()

            # <CASE STATEMENT> ::= SWITCH (<VARIABLE NAME>) { <CASE PART> }
            elif token == 'switch' and (statement[i] == ' ' or statement[i] == '('):
                return self.ProcessCaseStatement(statement[i : len(statement)])

            elif (token == 'case' and statement[i] == ' ') or (token == 'default' and statement[i] == ':'):
                return self.ProcessCasePart(statement)

            # <RETURN STATEMENT> ::= RETURN;
            elif token == 'return' and statement[i] == ';': # Needs a semi colon
                pass

            elif statement[i] == '{':
                self.NewCurlyBraceFound()
            
            elif statement[i] == '}':
                self.CloseCurlyBrace()

            # <PROCEDURE CALL STATEMENT> ::= <VARIABLE NAME> ( <VARIABLE PASS>
            elif statement[i] == '(':
                return self.ProcessProceduralCall(statement)

            # <ARRAY ASSIGNMENT STATEMENT> ::= <VARIABLE NAME>[<EXP><ARRAY ASSIGNMENT LIST>
            elif statement[i] == '[':
                return self.ProcessArrayAssignmentStatement(statement)

            elif token != '' and ((statement[i] == ' ' and statement[i + 1] == '=')  or statement[i] == '='):
                return self.ProcessAssignment(token, statement[i:len(statement)])
            
            elif statement[i] == ' ':
                continue
            else:
                token += statement[i]
            
            if token == 'else':
                return self.ProcessElseStatement()

    def ProcessStringAssignmentOrConcatenation(self, variable, expression):
        # variable has already been checked

        # expression = stringConstant | variableName | variableName + variableName with semi-colon
        variable1 = ''
        variable2 = ''
        stringConcat = False
        openStringConst = False
        closeStringConst = False

        for i in range(0, len(expression)):
            if expression[i] == ';':

                # stringConstant Assignment
                if openStringConst:
                    if not closeStringConst:
                        self._errorCount += 1
                        errorMessage = 'Syntax error on line ' + str(self._lineNumber) + '. Missing closing quotation in string declaration.'
                        self._errorMessages.append([self._lineNumber, errorMessage])
                    
                    elif not self.HasValidWordSyntax(variable1):
                        self._errorCount += 1
                        errorMessage = 'Error on line ' + str(self._lineNumber) + '. Invalid string expression.'
                        self._errorMessages.append([self._lineNumber, errorMessage])

                    result = self.GetStringConstantIfExists(variable1.replace('"', ''))
                    
                    if result == '':
                        result = '_s_' + str(self._varStringCount) + '_constString'
                        self._initializedValues.append(['string', result, variable1])
                        self._varStringCount += 1
                        self._operations.append(['stringVariableAssignment', result, '', variable])
                        self.SetVariableHasValue(variable)
                    
                    else:
                        self._operations.append(['stringVariableAssignment', result, '', variable])
                        self.SetVariableHasValue(variable)

                # single variable Assignment
                elif not openStringConst and variable2 == '':
                    self.PerformVariableCheck(variable1)
                    variable1Type = self.GetVariableType(variable1)

                    if variable1Type != 'string':
                        self._errorCount += 1
                        errorMessage = 'Semantic error on line ' + str(self._lineNumber) + '. The variable "' + variable1 + '" is not a string.'
                        self._errorMessages.append([self._lineNumber, errorMessage])
                    else:
                        tempOperand1 = self.GetVariableName(variable1)
                        self._operations.append(['stringVariableAssignment', tempOperand1, '', variable])
                        self.SetVariableHasValue(variable)

                # string concatenation assignment
                elif not openStringConst and variable2 != '':

                    self.PerformVariableCheck(variable1)
                    variable1Type = self.GetVariableType(variable1)

                    self.PerformVariableCheck(variable2)
                    variable2Type = self.GetVariableType(variable2)

                    if variable1Type != 'string':
                        self._errorCount += 1
                        errorMessage = 'Semantic error on line ' + str(self._lineNumber) + '. The variable "' + variable1 + '" is not a string.'
                        self._errorMessages.append([self._lineNumber, errorMessage])
                    elif variable2Type != 'string':
                        self._errorCount += 1
                        errorMessage = 'Semantic error on line ' + str(self._lineNumber) + '. The variable "' + variable2 + '" is not a string.'
                        self._errorMessages.append([self._lineNumber, errorMessage])

                    else:
                        tempOperand1 = self.GetVariableName(variable1)
                        tempOperand2 = self.GetVariableName(variable2)
                        self._operations.append(['stringConcatenationAssignment', tempOperand1, tempOperand2, variable])
                        self.SetVariableHasValue(variable)

            
            elif expression[i] == '"' and openStringConst:
                closeStringConst = True
            
            elif expression[i] == '"' and not openStringConst:
                openStringConst = True
            
            elif expression[i] == '+':
                stringConcat = True
                continue

            elif expression[i] == ' ' and not openStringConst:
                continue
            
            if stringConcat:
                variable2 += expression[i]
            else:
                variable1 += expression[i]


    def ProcessStringDeclarationStatement(self, statement):
        # statement = <VARIABLE NAME><DARTH VADER>
        # <DARTH VADER> ::= = <LUKE> | ;
        # <LUKE> ::= <VARIABLE NAME>; | <STRING CONSTANT>;
        # <STRING CONSTANT> ::= "<WORD>"

        lukeValue = ''
        variableName = ''
        findLuke = False
        openStringConst = False
        closeStringConst = False
        
        for i in range(0, len(statement)):
            if statement[i] == ';':
                #If it is just the variableName
                if lukeValue == '':
                    self.PerformNewVariableCheck(variableName) # Checks if the variableName has valid syntax and if the variableName is not already being used

                    variable = '_s_' + str(self._varStringCount) + '_' + variableName
                    self._uninitializedValues.append(['string', variable, 'no value'])
                    self._varStringCount += 1

                #If there is an assignment made
                elif lukeValue != '':
                    self.PerformNewVariableCheck(variableName) # Checks if the variableName has valid syntax and if the variableName is not already being used
                    
                    if not openStringConst and not closeStringConst: #Variable Assignment
                        
                        self.PerformVariableCheck(lukeValue)
                        lukeValueType = self.GetVariableType(lukeValue)

                        if lukeValueType != 'string':
                            self._errorCount += 1
                            errorMessage = 'Semantic error on line ' + str(self._lineNumber) + '. The variable "' + variableName + '" is not a string.'
                            self._errorMessages.append([self._lineNumber, errorMessage])
                        else:

                            variable = '_s_' + str(self._varStringCount) + '_' + variableName
                            self._varStringCount += 1
                            tempOperand1 = self.GetVariableName(lukeValue)

                            self._uninitializedValues.append(['string', variable, 'Has value'])
                            self._operations.append(['stringVariableAssignment', tempOperand1, '', variable])

                    else: # Const String assignment
                        
                        if not closeStringConst:
                            self._errorCount += 1
                            errorMessage = 'Syntax error on line ' + str(self._lineNumber) + '. Missing closing quotation in string declaration.'
                            self._errorMessages.append([self._lineNumber, errorMessage])
                        else:

                            variable = '_s_' + str(self._varStringCount) + '_' + variableName
                            self._varStringCount += 1
                            self._initializedValues.append(['string', variable, lukeValue])
            
            elif statement[i] == '=':
                findLuke = True
            
            elif findLuke:
                if statement[i] == '"' and not openStringConst:
                    openStringConst = True
                elif statement[i] == '"' and openStringConst:
                    closeStringConst = True
                elif statement[i] == ' ' and not openStringConst:
                    continue
                
                lukeValue += statement[i]
            
            elif statement[i] == ' ':
                continue
            else:
                variableName += statement[i]
            

    def ProcessVariablePass(self, procedureName, variablePass):
        # <VARIABLE PASS> ::= ); | <VARIABLES PASSED IN>
        # <VARIABLES PASSED IN> ::= <VARIABLE NAME><VARIABLES LISTED>
        # <VARIABLES LISTED> ::= ,<VARIABLES PASSED IN> | );

        closeParenFound = False
        variableName = ''
        variableParameterList = []
        procedureParameterList = []
        paramCount = 0

        if not self.ProcedureExists(procedureName):
            self._errorCount += 1
            errorMessage = 'Syntax error on line ' + str(self._lineNumber) + '. The procedure "' + procedureName + '" does not exist.'
            self._errorMessages.append([self._lineNumber, errorMessage])
        else:
            procedure = self.GetProcedure(procedureName)
            procedureParameterList = procedure[1]

        for i in range(0, len(variablePass)):
            
            if variablePass[i] == ')' and not closeParenFound:
                closeParenFound = True
                
                if variableName != '':

                    self.PerformVariableCheck(variableName)
                    
                    variable = self.GetVariableName(variableName)
                    parameterToAdd = [procedureName, variable, procedureParameterList[paramCount][3]]
                    variableParameterList.append(parameterToAdd)
                
                #Procedural check
                if not self.ParameterCountMatch(procedureName, variableParameterList):
                    self._errorCount += 1
                    errorMessage = 'Error on line ' + str(self._lineNumber) + '. Invalid number of parameters in procedure call.'
                    self._errorMessages.append([self._lineNumber, errorMessage])

                elif not self.ParameterTypeMatch(procedureName, variableParameterList):
                    self._errorCount += 1
                    errorMessage = 'Error on line ' + str(self._lineNumber) + '. Invalid types used in procedural call.'
                    self._errorMessages.append([self._lineNumber, errorMessage])


                self._operations.append(['procedureCall', procedureName, variableParameterList])

            elif not closeParenFound:
                
                if variablePass[i] == ',':
                    
                    self.PerformVariableCheck(variableName)
                    
                    variable = self.GetVariableName(variableName)
                    parameterToAdd = [procedureName, variable, procedureParameterList[paramCount][3]]
                    variableParameterList.append(parameterToAdd)
                    paramCount += 1
                    variableName = ''
                
                elif variablePass[i] == ' ':
                    continue
                else:
                    variableName += variablePass[i]


    def ProcessVariablePassing(self, procedureName, variablePassing):
        # <VARIABLE PASSING> ::= ) { <STATEMENT> } | <VARIABLE LIST>
        # <VARIABLE LIST> ::= <PASS BY VALUE> | <PASS BY REFERENCE>
        # <PASS BY REFERENCE> ::= NUM *<VARIABLE NAME><VARIABLE LISTING> | STRING *<VARIABLE NAME><VARIABLE LISTING>
        # <PASS BY VALUE> ::= NUM <VARIABLE NAME><VARIABLE LISTING> | STRING <VARIABLE NAME><VARIABLE LISTING>
        # <VARIABLE LISTING> ::= ,<VARIABLE LIST> | ) { <STATEMENT> }

        closeParenFound = False
        numFound = False
        stringFound = False
        passByReference = False
        variableName = ''
        variableType = ''
        variableParameterList = []

        for i in range(0, len(variablePassing)):
            
            if variablePassing[i] == ')' and not closeParenFound:
                closeParenFound = True
                self._procedureNeedsCurlyBrace = True
                
                if (numFound or stringFound) and variableName != '':
                    if not self.HasValidVariableSyntax(variableName):
                        self._errorCount += 1
                        errorMessage = 'Syntax error on line ' + str(self._lineNumber) + '. The variable "' + variableName + '" has invalid syntax.'
                        self._errorMessages.append([self._lineNumber, errorMessage])
                    else:
                        variable = ''

                        if not passByReference:
                            if variableType == 'num':
                                variable = '_n_' + str(self._varNumCount) + '_' + variableName

                                self._uninitializedValues.append(['num', variable, 'Has value'])
                                self._procedureParameters.append(['num', variable, 'Has value'])
                                self._varNumCount += 1
                            if variableType == 'string':
                                variable = '_s_' + str(self._varStringCount) + '_' + variableName
                                self._uninitializedValues.append(['string', variable, 'Has value'])
                                self._procedureParameters.append(['string', variable, 'Has value'])
                                self._varStringCount += 1
                        else:
                            if variableType == 'num':
                                variable = '_np_' + str(self._varNumCount) + '_' + variableName
                                self._uninitializedValues.append(['numPointer', variable, 'Has value'])
                                self._procedureParameters.append(['numPointer', variable, 'Has value'])
                                self._varNumCount += 1
                            elif variableType == 'string':
                                variable = '_sp_' + str(self._varStringCount) + '_' + variableName
                                self._uninitializedValues.append(['stringPointer', variable, 'Has value'])
                                self._procedureParameters.append(['stringPointer', variable, 'Has value'])
                                self._varStringCount += 1
                        
                        parameterToAdd = [procedureName, variableType, variable, passByReference]
                        variableParameterList.append(parameterToAdd)
                
                    #Procedural check
                    if self.ProcedureExists(procedureName):
                        self._errorCount += 1
                        errorMessage = 'Syntax error on line ' + str(self._lineNumber) + '. The procedure "' + procedureName + '" already exists.'
                        self._errorMessages.append([self._lineNumber, errorMessage])

                    self._procedures.append([procedureName, variableParameterList])
                    self._operations.append(['procedureDeclaration', procedureName, variableParameterList])

            elif closeParenFound and variablePassing[i] == '{':
                self.NewCurlyBraceFound()
                return self.ProcessStatement(variablePassing[i + 1: len(variablePassing)])

            elif not closeParenFound:
                
                if variablePassing[i] == ',' and (numFound or stringFound):
                    if not self.HasValidVariableSyntax(variableName):
                        self._errorCount += 1
                        errorMessage = 'Syntax error on line ' + str(self._lineNumber) + '. The variable "' + variableName + '" has invalid syntax.'
                        self._errorMessages.append([self._lineNumber, errorMessage])
                    else:
                        variable = ''

                        if not passByReference:
                            if variableType == 'num':
                                variable = '_n_' + str(self._varNumCount) + '_' + variableName
                                self._uninitializedValues.append(['num', variable, 'Has value'])
                                self._procedureParameters.append(['num', variable, 'Has value'])
                                self._varNumCount += 1
                            if variableType == 'string':
                                variable = '_s_' + str(self._varStringCount) + '_' + variableName
                                self._uninitializedValues.append(['string', variable, 'Has value'])
                                self._procedureParameters.append(['string', variable, 'Has value'])
                                self._varStringCount += 1
                        else:
                            if variableType == 'num':
                                variable = '_np_' + str(self._varNumCount) + '_' + variableName
                                self._uninitializedValues.append(['numPointer', variable, 'Has value'])
                                self._procedureParameters.append(['numPointer', variable, 'Has value'])
                                self._varNumCount += 1
                            elif variableType == 'string':
                                variable = '_s_' + str(self._varStringCount) + '_' + variableName
                                self._uninitializedValues.append(['stringPointer', variable, 'Has value'])
                                self._procedureParameters.append(['stringPointer', variable, 'Has value'])
                                self._varStringCount += 1
                        
                        parameterToAdd = [procedureName, variableType, variable, passByReference]
                        variableParameterList.append(parameterToAdd)
                        variableName = ''
                        variableType = ''
                        passByReference = False
                        numFound = False
                        stringFound = False

                elif numFound or stringFound:
                    if variablePassing[i] == '*':
                        passByReference = True
                    else:
                        variableName += variablePassing[i]
                
                elif variablePassing[i] == ' ' and not(numFound or stringFound):
                    if variableType == 'num':
                        numFound = True
                    elif variableType == 'string':
                        stringFound == True
                
                elif variablePassing[i] == ' ':
                    continue
                else:
                    variableType += variablePassing[i]


    def ProcessWriteStatement(self, alpha):

        # <ALPHA> ::= <EXP>; | "<WORD>"; | <VARIABLE NAME>
        # <VARIABLE NAME> ::= <LETTER><VARIABLE NAME PRIME>
        # <VARIABLE NAME PRIME> ::= <VAR CHARACTER><VARIABLE NAME PRIME> | e
        
        expression = ''
        variableName = ''
        openBracket = False
        closeBracket = False
        isStringConstant = False
        result = ''
        semicolonFound = False

        if not self.VariableNameExists('numberPrinter'):
            self._initializedValues.append(['numberPrinter', '"%d"'])
            self._variablesUsed.append('"%d"')
        if not self.VariableNameExists('stringPrinter'):
            self._initializedValues.append(['stringPrinter', '"%s"'])
            self._variablesUsed.append('"%s"')
        if not self.VariableNameExists('floatPrinter'):
            self._initializedValues.append(['floatPrinter', '"%f"'])
            self._variablesUsed.append('"%f"')

        for i in range(0, len(alpha)):
            
            if alpha[i] == ';':
                semicolonFound = True
                if isStringConstant:
                    
                    if not self.HasValidWordSyntax(expression):
                        self._errorCount += 1
                        errorMessage = 'Error on line ' + str(self._lineNumber) + '. Invalid string expression.'
                        self._errorMessages.append([self._lineNumber, errorMessage])

                    result = self.GetStringConstantIfExists(expression.replace('"', ''))
                    if result == '':
                        result = '_s_' + str(self._varStringCount) + '_constString'
                        self._initializedValues.append(['string', result, expression])
                        self._varStringCount += 1
                
                elif openBracket and closeBracket:
                    self.PerformVariableCheck(variableName)
                    #self.PerformArrayParameterCheck(expression)

                elif self.VariableNameExists(expression):
                    if self._constantPropagation:
                        result = self.GetVariableValue(self.GetVariableName(expression))
                    else:
                        result = self.GetVariableName(expression)
                else:
                    currentErrorCount = self._errorCount
                    result = self.ProcessExpression(expression + alpha[i], '')
                    if self._errorCount > currentErrorCount: # Invalid expression
                        self._errorCount += 1
                        errorMessage = 'Error on line ' + str(self._lineNumber) + '. Invalid expression.'
                        self._errorMessages.append([self._lineNumber, errorMessage])
                        
            elif alpha[i] == '"' and i == 0:
                isStringConstant = True
                expression += alpha[i]
            elif alpha[i] == '[':
                variableName = expression
                expression = ''
                openBracket = True
            elif alpha[i] == ']':
                closeBracket = True
            else:
                expression += alpha[i]

        if not semicolonFound:
            self._errorCount += 1
            errorMessage = 'Syntax error on line ' + str(self._lineNumber) + '. Missing semi-colon at end of statement.'
            self._errorMessages.append([self._lineNumber, errorMessage])
            return
        
        if openBracket and closeBracket:
            arrayList = []
            arrayListItem = ''
            for i in range(0, len(expression) + 1):
                if i == len(expression) or expression[i] == ',':
                    arrayList.append(arrayListItem)
                    arrayListItem = ''
                else:
                    arrayListItem += expression[i]
                    

            array = self.GetArray(variableName)
            delta = array[3]

            for j in range(len(arrayList)):
                if j == 0:
                    self._operations.append(['clearRegister'])

                if self.VariableNameExists(arrayList[j]):
                    self._operations.append(['arrayOffsetVariable', delta[j], arrayList[j]])
                else:
                    self._operations.append(['arrayOffset', delta[j], arrayList[j]])
            
            self._operations.append(['writeItemFromArray', array[4], 4, array[1]])
            return

        self._operations.append(['write', result])

    def SetVariableHasValue(self, variableName):
        listVariableName = ''

        for i in range(0, len(self._initializedValues)):

            _count = 0
            for j in range(0, len(self._initializedValues[i][1])):
                if self._initializedValues[i][1][j] == '_':
                    _count += 1
                if _count == 3:
                    listVariableName = self._initializedValues[i][1][j + 1 : len(self._initializedValues[i][1])]
                    break

            if listVariableName == variableName or variableName == self._initializedValues[i][1]:
                return

        for i in range(0, len(self._uninitializedValues)):

            _count = 0
            for j in range(0, len(self._uninitializedValues[i][1])):
                if self._uninitializedValues[i][1][j] == '_':
                    _count += 1
                if _count == 3:
                    listVariableName = self._uninitializedValues[i][1][j + 1 : len(self._uninitializedValues[i][1])]
                    break

            if listVariableName == variableName or variableName == self._uninitializedValues[i][1]:
                self._uninitializedValues[i][2] = 'Has value'
                return

        return


    def RefreshProcedureParameters(self, procedure):
        #self._procedures.append([procedureName, variableParameterList])
        variableParameterList = procedure[1]

        for variableParameter in variableParameterList:
            self.RemoveVariable(variableParameter[2])
        
    def RemoveCommentsFromStatement(self, statement): #returns string

        returnStatement = ''

        if self._multiLineCommentActive:
            endCommentIndex = statement.find('*/')
            if endCommentIndex == -1:
                return ''
            else:
                returnStatement = statement[endCommentIndex + 2: len(statement)]
                self._multiLineCommentActive = False
                return self.RemoveCommentsFromStatement(returnStatement)

        else:
            commentIndex = statement.find('//')
            
            if commentIndex != -1:
                returnStatement = statement[0:commentIndex]
                returnStatement += statement[len(statement) - 1: len(statement)]
                return self.RemoveCommentsFromStatement(returnStatement)
            
            commentEndIndex = statement.find('*/')
            commentBeginIndex = statement.find('/*')
            
            if (commentEndIndex < commentBeginIndex or commentBeginIndex == -1) and commentEndIndex != -1:
                
                errorMessage = 'Invalid syntax on line ' + str(self._lineNumber) + '.\n'
                self._errorCount += 1
                return errorMessage

            if (commentEndIndex > commentBeginIndex + 1) and commentBeginIndex != -1 and commentEndIndex != -1:
                returnStatement = statement[0:commentBeginIndex] + statement[commentEndIndex + 2: len(statement)]
                return self.RemoveCommentsFromStatement(returnStatement)
            
            if commentBeginIndex != -1:
                self._multiLineCommentActive = True
                returnStatement = statement[0:commentBeginIndex]
                returnStatement += statement[len(statement) - 1: len(statement)]
                return returnStatement
            
            return statement

    def RemoveVariable(self, variableName):

        listVariableName = ''

        for i in range(0, len(self._initializedValues)):

            _count = 0
            for j in range(0, len(self._initializedValues[i][1])):
                if self._initializedValues[i][1][j] == '_':
                    _count += 1
                if _count == 3:
                    listVariableName = self._initializedValues[i][1][j + 1 : len(self._initializedValues[i][1])]
                    break

            if listVariableName == variableName or variableName == self._initializedValues[i][1]:
                self._initializedValues.remove(self._initializedValues[i])
                return
                    

        for i in range(0, len(self._uninitializedValues)):

            _count = 0
            for j in range(0, len(self._uninitializedValues[i][1])):
                if self._uninitializedValues[i][1][j] == '_':
                    _count += 1
                if _count == 3:
                    listVariableName = self._uninitializedValues[i][1][j + 1 : len(self._uninitializedValues[i][1])]
                    break

            if listVariableName == variableName or variableName == self._uninitializedValues[i][1]:
                self._uninitializedValues.remove(self._uninitializedValues[i])
                return

    def UselessCodeRemoval(self, expression):
        
        processComplete = False
        openParenthesis = False

        if self._operatorCount == 0:
            return expression

        while not processComplete:

            index = 0
            tempOperatorIndex = 0
            tempOperator = ''
            tempOperand1Index = -1
            tempOperand2Index = -1
            tempOperand1 = ''
            tempOperand2 = ''
            tempVariable = ''
            tempOperators = []

            for char in expression:
                
                if char == ' ':
                    index += 1
                    continue
                else:
                    if self.IsOperator(char) or tempVariable == '':
                        if tempOperand1Index == -1 and (not self.IsOperator(char) or self.IsNegativeNumberIndex(index)):
                            tempOperand1Index = index
                        elif tempOperand2Index == -1 and (not self.IsOperator(char) or self.IsNegativeNumberIndex(index)):
                            tempOperand2Index = index
                        tempVariable = char
                    else:
                        tempVariable = tempVariable + char

                if expression[index + 1] == ' ' and not self.IsOperator(tempVariable):
                    if self.IsNumber(tempVariable) or self.VariableHasValue(tempVariable) or self.IsNegativeNumber(tempVariable) or self.IsFloatingPointNumber(tempVariable) or self.IsNegativeFloatingPointNumber(tempVariable):
                        if tempOperand1 == '':
                            if self.VariableHasValue(tempVariable):
                                tempOperand1 = self.GetVariableName(tempVariable)
                            else:
                                tempOperand1 = tempVariable
                            tempVariable = ''
                        elif index - 1 != tempOperatorIndex:
                            tempOperand2Index = index
                            if self.VariableHasValue(tempVariable):
                                tempOperand2 = self.GetVariableName(tempVariable)
                            else:
                                tempOperand2 = tempVariable
                elif self.IsOperator(tempVariable) and not self.IsNegativeNumberIndex(index) and not openParenthesis:
                    tempOperators.append([tempVariable, index])
                    tempOperatorIndex = index
                    tempOperator = tempVariable
                    tempVariable = ''
                    tempOperand1 = ''
                    tempOperand1Index = -1
                
                if tempOperand2 != '':
                    
                    uselessNumber = '0'
                    usefulParameter = ''
                    uselessOperationFound = False

                    if tempOperator == '*' or tempOperator == '/':
                        uselessNumber = '1'

                    if tempOperand1 == uselessNumber:  
                        uselessOperationFound = True
                        usefulParameter = tempOperand2
                    elif self.VariableNameExists(tempOperand1):
                        if self.GetVariableValue(tempOperand1) == uselessNumber:
                            uselessOperationFound = True
                            usefulParameter = tempOperand2
                    
                    if tempOperand2 == uselessNumber and not uselessOperationFound:
                        uselessOperationFound = True
                        usefulParameter = tempOperand1
                    elif self.VariableNameExists(tempOperand2) and not uselessOperationFound:
                        if self.GetVariableValue(tempOperand2) == uselessNumber:
                            uselessOperationFound = True
                            usefulParameter = tempOperand1
                    
                    if uselessOperationFound:
                        self._operatorCount -= 1
                        if tempOperatorIndex == 0:
                            expression = expression[tempOperatorIndex + 1: len(expression)]
                        else:
                            expression = expression[0:tempOperatorIndex] + expression[tempOperatorIndex + 1: len(expression)]

                        if tempOperand1Index == 0 or tempOperand1Index - 1 == 0:
                            expression = usefulParameter + expression[tempOperand2Index: len(expression)]
                            break
                        else:
                            expression = expression[0:tempOperand1Index - len(tempOperand1)] + usefulParameter + expression[tempOperand2Index: len(expression)]
                            if self.IsNegativeNumber(usefulParameter):
                                self._negativeNumberIndexes.append(tempOperand1Index - len(tempOperand1))
                            if expression[0] == ' ':
                                expression = expression[1: len(expression)]
                            break
                    
                    index += 1
                else:
                    index += 1

            if tempOperand2 == '':
                processComplete = True

        return expression

    def VariableHasValue(self, variableName):
        
        listVariableName = ''

        for i in range(0, len(self._initializedValues)):

            _count = 0
            for j in range(0, len(self._initializedValues[i][1])):
                if self._initializedValues[i][1][j] == '_':
                    _count += 1
                if _count == 3:
                    listVariableName = self._initializedValues[i][1][j + 1 : len(self._initializedValues[i][1])]
                    break

            if listVariableName == variableName or self._initializedValues[i][1] == variableName:
                return True

        for i in range(0, len(self._uninitializedValues)):

            _count = 0
            for j in range(0, len(self._uninitializedValues[i][1])):
                if self._uninitializedValues[i][1][j] == '_':
                    _count += 1
                if _count == 3:
                    listVariableName = self._uninitializedValues[i][1][j + 1 : len(self._uninitializedValues[i][1])]
                    break

            if listVariableName == variableName or self._uninitializedValues[i][1] == variableName:
                if self._uninitializedValues[i][2] != 'no value':
                    return True

        return False


    def VariableNameExists(self, variableName):

        listVariableName = ''

        for i in range(0, len(self._tempVariables)):
            if variableName == self._tempVariables[i]:
                return True

        for i in range(0, len(self._initializedValues)):

            if(variableName.find("Printer") != -1):
                if self._initializedValues[i][0] == variableName:
                    return True
            else:
                _count = 0
                for j in range(0, len(self._initializedValues[i][1])):
                    if self._initializedValues[i][1][j] == '_':
                        _count += 1
                    if _count == 3:
                        listVariableName = self._initializedValues[i][1][j + 1 : len(self._initializedValues[i][1])]
                        break

                if listVariableName == variableName or self._initializedValues[i][1] == variableName:
                    return True

        for i in range(0, len(self._uninitializedValues)):

            _count = 0
            for j in range(0, len(self._uninitializedValues[i][1])):
                if self._uninitializedValues[i][1][j] == '_':
                    _count += 1
                if _count == 3:
                    listVariableName = self._uninitializedValues[i][1][j + 1 : len(self._uninitializedValues[i][1])]
                    break

            if listVariableName == variableName or self._uninitializedValues[i][1] == variableName:
                return True

        return False
    
    def VariableInWriteStatement(self, variable):
        # _writeOperationVariableDependencies
        for writeOperationVariable in self._writeOperationVariables:
            if writeOperationVariable == variable:
                return True
        return False
    
    def VariableIsADependencyToWriteStatment(self, variable):

        for writeOperationVariableDependency in self._writeOperationVariableDependencies:
            if writeOperationVariableDependency == variable:
                return True
        return False
    
def main():
    Compiler().CompilerMain()
    
if __name__ == "__main__":
    main()