class Security:
    def __init__(self, name):
        self.name = name
        self.transactions = []
        self.total_shares = 0

    def issue(self, shares, issuer, stock_class):
        tx = Transaction(self, issuer, stock_class, shares)
        self.transactions.append(tx)
        self.total_shares += shares

    def cancel(self, shares):
        if shares <= self.total_shares:
            tx = Transaction(self, None, None, -shares)
            self.transactions.append(tx)
            self.total_shares -= shares
            # Must create the balancing security
            # but there is nothing to call - 
            # this is not the role of this class,
            # so the model is not very good.

        else:
            raise ValueError("Cannot cancel more shares than exist")

    def transfer(self, shares, to_security, from_issuer=None, to_issuer=None):
        if shares <= self.total_shares:
            tx = Transaction(self, to_security, to_issuer, shares)
            self.transactions.append(tx)
            self.total_shares -= shares
            to_security.total_shares += shares
        else:
            raise ValueError("Cannot transfer more shares than exist")
