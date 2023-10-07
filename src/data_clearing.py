# -*- coding: utf-8 -*-
"""Data Preparation

Inspired by https://www.kaggle.com/code/essammohamed4320/credit-score-classification/notebook by ESSAM MOHAMED

Authored by Ying Yue


"""




# Importing necessary Libraries
import warnings
import pandas as pd
import numpy as np

import seaborn as sns
from sklearn import preprocessing


NUMS_DATA = 2000

print("hello world")

def main():

    pd.set_option('display.max_columns',None)
    warnings.filterwarnings('ignore')
    # %matplotlib inline

    # Loading and Exploring Data
    df = pd.read_csv("data/train.csv")

    # Dropping irrelevant features
    df_c = df.copy()
    df_c.drop(['ID' ,'Customer_ID' ,'Month' ,'Name', 'Type_of_Loan', 'Credit_History_Age', 'SSN', 'Credit_Mix'], axis=1, inplace=True)

    # Dropping all observations with more than 3 missing values
    size_before_cleaning = df_c.shape
    df_c = df_c[df_c.isnull().sum(axis=1) < 3]
    # print("{} Records dropped".format(size_before_cleaning[0] - df_c.shape[0]))

    def filter_general(value):
        if '-' in str(value):
            return str(value).split('-')[1]
        elif '_' in str(value):
            return str(value).split('_')[0]
        else:
            return str(value)

    def filter_delayed_payments(value):
        if "__" in str(value):
            return str(value).split("__")[1]
        elif '_' in str(value):
            return str(value).replace("_", "")
        elif str(value) == '_':
            return str(value)
        else:
            return str(value)

    def Amount_invested_monthly(col):
        if "__" in str(col):
            return str(col).split("__")[1]
        else:
            return str(col)

    df_c["Amount_invested_monthly"]=df_c["Amount_invested_monthly"].apply(Amount_invested_monthly)
    df_c["Amount_invested_monthly"]=df_c["Amount_invested_monthly"].astype("float")

    df_c["Changed_Credit_Limit"]=df_c["Changed_Credit_Limit"].apply(lambda x:x.split("-")[-1])
    df_c.drop(df_c[df_c["Changed_Credit_Limit"]=="_"].index,inplace=True)
    df_c["Changed_Credit_Limit"]=df_c["Changed_Credit_Limit"].astype("float")

    df_c.drop(df_c[df_c["Monthly_Balance"]=='__-333333333333333333333333333__'].index,inplace=True)
    for i in ['Age', 'Annual_Income', 'Num_of_Loan', 'Outstanding_Debt', 'Monthly_Balance']:
        df_c[i] = df_c[i].apply(filter_general)
        df_c[i] = df_c[i].astype(np.float64)


    df_c['Num_of_Delayed_Payment'] = df_c['Num_of_Delayed_Payment'].apply(filter_delayed_payments)
    df_c['Num_of_Delayed_Payment'] = df_c['Num_of_Delayed_Payment'].astype(np.float64)

    df_c['Occupation'] = df_c['Occupation'].replace('_______', np.nan)
    df_c['Occupation'] = df_c['Occupation'].fillna(np.random.choice(pd.Series(['Scientist', 'Teacher', 'Engineer', 'Entrepreneur',
        'Developer', 'Lawyer', 'Media_Manager', 'Doctor', 'Journalist',
        'Manager', 'Accountant', 'Musician', 'Mechanic', 'Writer',
        'Architect'])))

    # df_c['Credit_Mix'] = df_c['Credit_Mix'].replace('_', np.nan)
    # df_c['Credit_Mix'] = df_c['Credit_Mix'].fillna(np.random.choice(pd.Series(['Standard', 'Good', 'Bad'])))

    df_c['Payment_of_Min_Amount'] = df_c['Payment_of_Min_Amount'].replace('NM', np.nan)
    df_c['Payment_of_Min_Amount'] = df_c['Payment_of_Min_Amount'].fillna(np.random.choice(pd.Series(['Yes', 'No'])))

    df_c['Payment_Behaviour'] = df_c['Payment_Behaviour'].replace('!@9#%8', np.nan)
    df_c['Payment_Behaviour'] = df_c['Payment_Behaviour'].fillna(np.random.choice(pd.Series(['High_spent_Small_value_payments',
        'Low_spent_Large_value_payments', 'Low_spent_Small_value_payments',
        'High_spent_Medium_value_payments',
        'High_spent_Large_value_payments',
        'Low_spent_Medium_value_payments'])))

    for i in ['Monthly_Inhand_Salary', 'Num_of_Delayed_Payment', 'Num_Credit_Inquiries', 'Amount_invested_monthly']:
        df_c[i].fillna(df_c[i].median(), inplace=True)

    df_c['Monthly_Balance'].fillna(df_c['Monthly_Balance'].median(), inplace=True)


    numeric_cols = df_c.select_dtypes(exclude = "object").columns
    cat_cols = df_c.select_dtypes(include = "object").columns

    df_c_n = df_c.copy()
    for i in numeric_cols:
        ''' Detection '''
        # IQR
        Q1 = np.percentile(df_c_n[i], 0.05,interpolation = 'midpoint')
        Q3 = np.percentile(df_c_n[i], 99.95,interpolation = 'midpoint')
        # print("@ Feature " + i + "...")
        # print("Old Shape: ", df_c_n.shape)
        df_c_n[numeric_cols] = df_c_n[numeric_cols][(df_c_n[i] < Q3) & (df_c_n[i] > Q1)]
        df_c_n.dropna(inplace=True)
        # print("New Shape: ", df_c_n.shape)
    df_c_n.drop(df_c_n[df_c_n["Age"] >= 80].index, inplace=True)
    df_c_n.drop(df_c_n[df_c_n["Annual_Income"] >= 500000].index, inplace=True)
    df_c_n.drop(df_c_n[df_c_n["Num_Bank_Accounts"] >= 20].index, inplace=True)
    df_c_n.drop(df_c_n[df_c_n["Num_Credit_Card"] >= 50].index, inplace=True)
    df_c_n.drop(df_c_n[df_c_n["Num_of_Loan"] >= 20].index, inplace=True)
    df_c_n.drop(df_c_n[df_c_n["Interest_Rate"] >= 35].index, inplace=True)
    df_c_n.drop(df_c_n[df_c_n["Num_of_Delayed_Payment"] >= 30].index, inplace=True)
    df_c_n.drop(df_c_n[df_c_n["Num_Credit_Inquiries"] >= 100].index, inplace=True)
    df_c_n.drop(df_c_n[df_c_n["Total_EMI_per_month"] >= 2000].index, inplace=True)
    df_c_n.drop(df_c_n[df_c_n["Amount_invested_monthly"] >= 1000].index, inplace=True)

    # Handling numirical data
    numeric_cols = df_c.select_dtypes(exclude = "object").columns
    cat_cols = df_c.select_dtypes(include = "object").columns
    # print(numeric_cols)
    # print(cat_cols)
    df_num_clean = df_c_n[numeric_cols].copy()
    cols = numeric_cols

    def RobustScaling(df_num, cols):
        scaler = preprocessing.RobustScaler()
        robust_df_temp = scaler.fit_transform(df_num)
        robust_df_temp = pd.DataFrame(robust_df_temp, columns =cols)
        return robust_df_temp

    robust_scaled = RobustScaling(df_num_clean, numeric_cols)

    clean_df = df_c.copy()
    clean_df.drop(labels=numeric_cols, axis="columns", inplace=True)
    clean_df[numeric_cols] = robust_scaled[numeric_cols]
    # clean_df.head()

    # Categorical data encoding
    clean_df['Credit_Score'].replace({"Poor":0, "Standard":1, "Good":1}, inplace=True)
    # clean_df['Credit_Mix'].replace({"Bad":0, "Standard":1, "Good":2}, inplace=True)
    clean_df['Payment_of_Min_Amount'].replace({"Yes":1, "No":0}, inplace=True)
    clean_df = pd.get_dummies(clean_df, columns = ['Occupation', 'Payment_Behaviour'])
    #clean_df = clean_df.drop("Credit_Mix",'columns')

    for i in numeric_cols:
        clean_df[i].fillna(method='ffill', inplace=True)

    # cut part of the dataset
    clean_df = clean_df[:NUMS_DATA]
    print("data cleaning completed. results as follows:")
    clean_df.head()
    print("data info:")
    clean_df.info()

    clean_df.to_csv("data/cleaned_data.csv")






if __name__ == '__main__':
    main()

