import sys
import re
import argparse

parser = argparse.ArgumentParser()
parser.add_argument("holes_list", nargs='+', default=[])
parser.add_argument("-input-path", help="Path to the input files to be parsed")
parser.add_argument("-file-name", help="Name of the file that is used for hole evaluation")
args = parser.parse_args()

input_path = str(args.input_path)
holes = args.holes_list
filename = str(args.file_name)

for id in holes:
    with open(input_path + '/output_' + filename + '_' + id + '/output.txt') as f:
        lines = f.readlines()
        correctAnswer = []
        firstCorrectAnswerLineNo = -1
        for i, line in enumerate(lines):
            match = re.search('correct answer', line)
            if match is not None:
                if firstCorrectAnswerLineNo == -1:
                    firstCorrectAnswerLineNo = i
                sp = line.split(':')
                correctAnswer.append(''.join(sp[3:])[1:-1])
            match = re.search(' finish exploring', line)
            if match is not None:
                finishExploringLineNo = i
            match = re.search('IncorrectProof', line)
            if match is not None:
                resultSummary = list(filter(None, lines[i+1].split(' ')))[:-1]
        if firstCorrectAnswerLineNo != -1:
            numberOfExpressions = int((str(lines[firstCorrectAnswerLineNo - 1]).split(" "))[0]) + 1
            firstCorrectAnswerFoundAt = (str(lines[firstCorrectAnswerLineNo]).split(" "))[0]
            firstAnswerAt = (str(lines[firstCorrectAnswerLineNo]).split(" "))[0][:-2]
        else:
            numberOfExpressions = int((str(lines[finishExploringLineNo - 2]).split(" "))[0]) + 1
            firstAnswerAt = 0
        execTime = (str(lines[finishExploringLineNo]).split(" "))[0][:-2]
        print (id, numberOfExpressions, round(float(float(execTime)/60), 2), round(float(float(firstAnswerAt)/60), 2), len(correctAnswer), 'TRUE' if 'true' in correctAnswer else '', sep = ',')
        print (*resultSummary, sep=',')
        if 'true' in correctAnswer:
            print ('***true***')
        else:
            print(*correctAnswer, sep = '\n')
    with open(input_path + '/output_' + filename + '_' + id + '/executionTimeSummary.txt') as f:
        lines = f.readlines()
        lessThanOneSec = 0
        lessThanOneMin = 0
        lessThanTenMin = 0
        other = 0
        sum = 0
        for i, line in enumerate(lines):
            sp = line.split(' ')
            t = float(sp[1])
            if t < 1:
                lessThanOneSec = lessThanOneSec + 1
            elif t < 60:
                lessThanOneMin = lessThanOneMin + 1
            elif t < 600:
                lessThanTenMin = lessThanTenMin + 1
            else:
                other = other + 1
            sum = sum + t
        print('', lessThanOneSec, lessThanOneMin, lessThanTenMin, other, round(sum / len(lines), 2), sep=',')


