I think some concepts defined as enums or types in the OCF can be best modeled in Alloy by using abstract signatures and signature extension. 
For example, a stakeholder can be a person but can also be an institutional investor. In the latter case, the stakeholder is not a person but an organization, which in the case of another company itself can issue securities. 

This new relationship that the model would be able to express is exactly the relationship which is needed for calculating taxes or dividends (and many other accounting and financial figures) in the case of cross-holdings.