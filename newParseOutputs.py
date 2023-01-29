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
        breakdown = (str(lines[finishExploringLineNo+2]).split(" "))
        breakdown = [i for i in breakdown if i]
        #print (id, numberOfExpressions, round(float(float(execTime)/60), 2), round(float(float(firstAnswerAt)/60), 2), breakdown[0], breakdown[1], breakdown[2], breakdown[3], breakdown[4], 'TRUE' if 'true' in correctAnswer else '', sep = ',')
        #print (*resultSummary, sep=',')
        if 'true' in correctAnswer:
            print ('***true***')
        else:
            print(*correctAnswer, sep = ';')
