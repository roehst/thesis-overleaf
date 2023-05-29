How can JSON Schema be mapped to Alloy?

A simple example can be given to show a general picture.

Suppose we are modeling securities and the issuance transaction.

The schemas could reasonably be given as:

```json
{
    "type": "security",
    "properties": {
        "id": {
            "type": "string"
        },
    }
}
```

```json
{
    "type": "issuance_transaction",
    "properties": {
        "id": {
            "type": "string"
        },
        "security_id": {
            "type": "string"
        },
        "shares": {
            "type": "number"
        }, 
        "issuer_id": {
            "type": "string"
        }
    }
}
```

Step 1. Translate the sigs

In order to translate to Alloy, first we lay out the signatures:

```Alloy
sig Id {}

sig Security {
    id : Id
}

sig Issuer {
    id : Id
}

sig IssuanceTransaction {
    id : Id,
    security : Security,
    shares : Int,
    issuer : Issuer
}
```

And then we can give quickly improve the model by adding a constraint so that no security has two issuances:

```alloy
fact {
    no i, j : IssuanceTransaction | i.security = j.security and i != j
}
```


