import os
import sys
import argparse
import numpy as np

def convert_file_to_sentence(train_file_list):
    split_text = []
    for file in train_file_list:
        f = open(file)
        text = f.readlines()
        split_text = split_text + split_sentence(text)
        f.close()
    # print(split_text)
    return split_text


def split_sentence(text):
    """ return a nested list where the inner list are seperated by the PUN
    result list example:
     [['Detective : NP0', 'Chief : NP0', '. : PUN'],
     ['he : PNP', 'was : VBD', 'hungry : AJ0', ', : PUN'] ... ]
    """
    result = []
    current_sentence = []
    for line in text:

        cur_train_line = line.strip('\n')
        cur_train_word = cur_train_line.split(' : ')[0]
        current_sentence.append(cur_train_line)
        if cur_train_word == '.' or cur_train_word == '!' or cur_train_word == '?' \
                or cur_train_word == '"':
            result.append(current_sentence)
            current_sentence = []

    if len(current_sentence) != 0:
        result.append(current_sentence)
    return result


def training(train_list):
    # get probability for HMM"

    # header_count is counting the time the tag exist in the begging of the sentence
    # {'Detective': 1, 'Having': 1}
    header_count = {}

    # prev_count has tag as the key and stole the another tag with the time that tag occurs before the key tag
    # {'NPO': {'NPO': 4}, 'VVD': {'NPO':1}}
    prev_count = {}

    # word_exist_count has tag as the key and stole the word with this tag and the times this word occurs
    # {'NPO':{'Detective': 1, 'Chief': 1}, 'VVD': {'gazed': 1}}
    word_exist_count = {}

    # number of this tag exist.
    # {'NPO':5, 'VVD':1}
    tag_count = {}
    tag_list = []

    list_sentence = convert_file_to_sentence(train_list)
    num_sentence = len(list_sentence)

    #update the counts
    for sentence in list_sentence:
        header_count, prev_count, tag_count, word_exist_count, tag_list \
            = update_counts(header_count, prev_count,
                            tag_count, word_exist_count,
                            tag_list, sentence)
    
    header_prob = dict()
    prev_prob = dict()
    word_prob = dict()

    for key in header_count:
        header_prob[key] = header_count[key] / num_sentence

    for key in prev_count:
        prev_prob[key] = dict()
        for tag in prev_count[key]:
            prev_prob[key][tag] = prev_count[key][tag]/tag_count[tag]

    for key in word_exist_count:
        word_prob[key] = dict()
        for word in word_exist_count[key]:
            word_prob[key][word] = word_exist_count[key][word] / tag_count[key]

    return header_prob, prev_prob, word_prob, tag_count, tag_list

def viterbi_algorithm(header_prob, prev_prob, word_prob, tag_count, tag_list, sentence):
    """Finds the most likely tag sequence for the input sentence using Viterbi algorithm."""
    prob = np.zeros((len(sentence), len(tag_list)))
    prev = np.zeros((len(sentence), len(tag_list)))

    start_ob = False
    for tag_ in tag_list:
        if sentence[0] in word_prob[tag_] and tag_ in header_prob:
            start_ob = True
            break
    for j in range(len(tag_list)):
        if not start_ob:
            if tag_list[j] in header_prob:
                prob[0, j] = header_prob[tag_list[j]]
        elif tag_list[j] in header_prob and sentence[0] in word_prob[tag_list[j]]:
            prob[0, j] = header_prob[tag_list[j]] * word_prob[tag_list[j]][sentence[0]]
        prev[0, j] = None

    for word in range(1, len(sentence)):
        w_obs = False
        for tag2 in tag_list:
            if sentence[word] in word_prob[tag2] and tag2 in prev_prob:
                w_obs = True
        prob_state = prob[word-1].reshape((1, prob[word-1].shape[0])).repeat(len(tag_list), axis=0)
        word_state = []
        trans_state = []
        for i in range(len(tag_list)):
            if not w_obs:
                word_state.append(1)
            elif sentence[word] in word_prob[tag_list[i]]:
                word_state.append(word_prob[tag_list[i]][sentence[word]])
            else:
                word_state.append(0)
            #calculate trans
            trans = []
            for j in range(len(tag_list)):
                if tag_list[i] in prev_prob and tag_list[j] in prev_prob[tag_list[i]]:
                    trans.append(prev_prob[tag_list[i]][tag_list[j]])
                else:
                    trans.append(1/tag_count[tag_list[j]])
            trans_state.append(trans)
        word_state = np.array(word_state).reshape((len(tag_list), 1))
        trans_state = np.array(trans_state)
        state = np.multiply(np.multiply(prob_state, trans_state),word_state)
        max_state = state.max(axis=1)
        max_state = np.divide(max_state, max_state.sum())
        max_ = state.argmax(axis=1)
        prob[word] = max_state
        prev[word] = max_

    return prob, prev

def update_counts(header_count, prev_count, tag_count, word_exist_count, tag_list, sentence):
    prev_tag = None
    for i in range(len(sentence)):
        word, cur_tag = sentence[i].split(' : ')
        if cur_tag not in tag_list:
            tag_list.append(cur_tag)

        if i == 0:
            if cur_tag not in header_count:
                header_count[cur_tag] = 1
            else:
                header_count[cur_tag] += 1
        else:
            if cur_tag not in prev_count:
                prev_count[cur_tag] = dict()
                prev_count[cur_tag][prev_tag] = 1
            else:
                if prev_tag not in prev_count[cur_tag]:
                    prev_count[cur_tag][prev_tag] = 1
                else:
                    prev_count[cur_tag][prev_tag] += 1

        if cur_tag not in tag_count:
            tag_count[cur_tag] = 1
        else:
            tag_count[cur_tag] += 1

        if cur_tag not in word_exist_count:
            word_exist_count[cur_tag] = dict()
            word_exist_count[cur_tag][word] = 1
        else:
            if word not in word_exist_count[cur_tag]:
                word_exist_count[cur_tag][word] = 1
            else:
                word_exist_count[cur_tag][word] += 1

        prev_tag = cur_tag
    return header_count, prev_count, tag_count, word_exist_count, tag_list

def tag(train_list, test_file, output_file):
    header_prob, prev_prob, word_prob, tag_count, tag_list = training(train_list)
    f_r = open(test_file)
    sentence_list = f_r.readlines()
    single_sentence = split_sentence(sentence_list)
    f_w = open(output_file, 'w')
    index = 0
    text_and_tag = []
    for word in single_sentence:
        prob, prev = viterbi_algorithm(header_prob, prev_prob, word_prob, tag_count, tag_list, word)
        text_and_tag += read_prev(tag_list, prob, prev, word)
    print('finish tagging, start writing')
    for output in text_and_tag:
        f_w.write(output + '\n')




def read_prev(tag_list, prob, prev, sentence: list):
    """Return the output of the most likely tag sequence with a given sentence"""
    # Find the highest probability at the last word of the sentence
    last_max = 0
    last_max_ind = None
    tag_result = []
    for i in range(prob.shape[1]):
        if prob[prob.shape[0] - 1, i] > last_max:
            last_max = prob[prob.shape[0] - 1][i]
            last_max_ind = i
    # Backward traverse the most likely path
    for i in range(prev.shape[0] - 1, -1, -1):
        tag_result.append(sentence[i] + ' : ' + tag_list[last_max_ind])
        if i != 0:
            last_max_ind = int(prev[i, last_max_ind])
    tag_result.reverse()

    return tag_result


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--trainingfiles",
        action="append",
        nargs="+",
        required=True,
        help="The training files."
    )
    parser.add_argument(
        "--testfile",
        type=str,
        required=True,
        help="One test file."
    )
    parser.add_argument(
        "--outputfile",
        type=str,
        required=True,
        help="The output file."
    )
    args = parser.parse_args()

    training_list = args.trainingfiles[0]
    print("training files are {}".format(training_list))

    print("test file is {}".format(args.testfile))

    print("output file is {}".format(args.outputfile))

    print("Starting the tagging process.")
    tag(training_list, args.testfile, args.outputfile)
