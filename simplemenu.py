import tssml;

# Defining child class
class Child(tssml.TSSMLDriver):
    def get_customized_values(self):
        pass



obj1=Child()
obj1.start_interactive()
