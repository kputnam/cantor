# encoding: UTF-8
require "spec_helper"

describe Cantor::AbsoluteSet do

  def mksubset(universe)
    universe.copy(:mask => rand(2**universe.size))
  end

  def mksingleton(universe)
    universe.copy(:mask => (2**(rand(universe.size) + 1) >> 1))
  end

  def self.items;    %w(a b c d e f g h i j k l m n o p q r s t u v w x y z) end
  def self.universe; Cantor.absolute(items)                                  end
  def self.single;   universe.copy(:mask => 0b00000000000000000000000001)    end
  def self.subset;   universe.copy(:mask => 0b10101010101010101010101010)    end
  def self.null;     universe.copy(:mask => 0b00000000000000000000000000)    end

  let(:items)    { %w(a b c d e f g h i j k l m n o p q r s t u v w x y z) }
  let(:universe) { Cantor.absolute(items)                                  }
  let(:single)   { universe.copy(:mask => 0b00000000000000000000000001)    }
  let(:subset)   { universe.copy(:mask => 0b10101010101010101010101010)    }
  let(:null)     { universe.copy(:mask => 0b00000000000000000000000000)    }

  def self.property(*args)
    # TODO: Use Propr
    @p ||= Class.new do
      def check(*args)
        self
      end
    end.new
  end

  describe "#to_a" do
    property("|A| == |A.to_a|"){|xs| xs.size == xs.to_a.size }.
      check(null).
      check(single).
      check(subset).
      check(universe)

    property("x ∉ A => x ∉ A.to_a") do |a, to_a|
      universe.all? do |x|
        a.include?(x) or not to_a.include?(x)
      end
    end.check { bind(mksubset(universe)) { unit([a, a.to_a]) }}

    property("x ∈ A => x ∈ A.to_a") do |a, to_a|
      universe.all? do |x|
        not a.include?(x) or to_a.include?(x)
      end
    end.check { bind(mksubset(universe)) { unit([a, a.to_a]) }}
  end

  describe "#first" do
    property("{x}.first = x"){|a,x| a.first == x }.
      check{ bind(mkelement(universe)){|x| unit([universe & [x], x]) }}

    property("A.first ∈ A"){|a| guard(!a.empty?); a.include?(a.first) }.
      check{|a| mksubset(universe) }
  end

  describe "#map(&block)" do
    property("A.map{|a| a } = A"){|s| expect(s.map{|a| a }).to eq(a) }.
      check(null).
      check(single).
      check(subset).
      check(universe).
      check{ mksubset(universe) }

    specify "A.map{|a| b } raises an error, given b ∉ U and A ≠ ∅" do
      expect { single.map{|a| "A" }}.to \
        raise_error(/universe does not contain element/)

      expect { subset.map{|a| "A" }}.to \
        raise_error(/universe does not contain element/)

      expect { universe.map{|a| "A" }}.to \
        raise_error(/universe does not contain element/)
    end

    property("A.map{|a| b } = {b}, given b ∈ U, A ≠ ∅") do |xs, x|
      xs.map{|a| x } == [x]
    end.
      check(single, "a").
      check(subset, subset.first).
      check(universe, "z").
      check{ bind(mksubset(universe)){|xs| bind(mkelement(xs)) {|x| unit [xs, x] }}}
  end

  describe "#select(&block)" do
    property("A.select{|a| true } = A"){|xs| xs.select{|a| true } == xs }.
      check(null).
      check(single).
      check(subset).
      check(universe).
      check{ mksubset(universe) }

    property("A.select{|a| false } = ∅"){|xs| xs.select{|a| false } == null }.
      check(null).
      check(single).
      check(subset).
      check(universe).
      check{ mksubset(universe) }

    property("A.select{|a| a == b } = {b}, given b ∈ U, A ≠ ∅") do |xs, x|
      guard(!xs.empty?)
      xs.select{|a| a == x } == [x]
    end.
      check(single).
      check(subset).
      check(universe).
      check{ bind(mksubset(universe)){|xs| bind(mkelement(xs)){|x| unit [xs, x] }}}
  end

  describe "#reject(&block)" do
    property("A.reject{|a| false } = A") do |xs|
      xs.reject{|a| false } == xs
    end.
      check(null).
      check(single).
      check(subset).
      check(universe).
      check{ mksubset(universe) }

    property("A.reject{|a| true } = ∅") do
      expect(subset.reject{|a| true }).to eq(null)
    end.
      check(null).
      check(single).
      check(subset).
      check(universe).
      check{ mksubset(universe) }

    specify "A.reject{|a| a != b } = {b}, given b ∈ U, A ≠ ∅" do
    end

    property("A.reject{|a| a != b } = {b}, given b ∈ U, A ≠ ∅") do |xs, x|
      guard(!xs.empty?)
      xs.reject{|a| a != e } == [e]
    end.
      check(single).
      check(subset).
      check(universe).
      check{ bind(mksubset(universe)){|xs| bind(mkelement(xs)){|x| unit [xs, x] }}}
  end

  describe "#include?(element)" do
    specify "x ∉ ∅, for all x" do
      expect(null).to_not include("a")
      expect(null).to_not include("A")
    end

    specify "x ∉ A, for all x ∉ U" do
      expect(single).to_not include("A")
      expect(subset).to_not include("A")
      expect(universe).to_not include("A")
    end

    specify "x ∈ {x}, for all x" do
      expect(single).to include("a")
    end

    property("x ∈ {x}, for all x") do
      mksingleton(universe)
    end.check do |singleton|
      expect(singleton).to include(singleton.first)
    end

    property("x ∉ A, for all x ∈ ¬A") do
      mksubset(universe)
    end.check do |a|
      (~a).each{|e| expect(a).to_not include(e) }
    end
  end

  describe "#finite?" do
    it "is true" do
      expect(null).to be_finite
      expect(single).to be_finite
      expect(subset).to be_finite
      expect(universe).to be_finite
    end
  end

  describe "#empty?" do
    specify "∅.empty? is true" do
      expect(null).to be_empty
    end

    specify "{x}.empty? is false" do
      expect(single).to_not be_empty
    end
  end

  describe "#present?" do
    specify "∅.present? is false" do
      expect(null).to_not be_present
    end

    specify "{x}.present? is true" do
      expect(single).to be_present
    end
  end

  describe "#size" do
    specify "∅.size == 0" do
      null.size == 0
    end

    specify "{x}.size == 1" do
      expect(single.size).to eq(1)
    end
  end

  describe "#complement" do
    specify "A ∩ ¬A = ∅" do
      expect((null & ~null)).to eq(null)
      expect((single & ~single)).to eq(null)
      expect((subset & ~subset)).to eq(null)
      expect((universe & ~universe)).to eq(null)
    end

    property("A ∩ ¬A = ∅") do
      mksubset(universe)
    end.check do |a|
      expect((a & ~a)).to eq(null)
    end

    specify "A ∪ ¬A = U" do
      expect((null | ~null)).to eq(universe)
      expect((single | ~single)).to eq(universe)
      expect((subset | ~subset)).to eq(universe)
      expect((universe | ~universe)).to eq(universe)
    end

    property("A ∪ ¬A = U") do
      mksubset(universe)
    end.check do |a|
      expect((a | ~a)).to eq(universe)
    end

    specify "A ⊖ ¬A = U" do
      expect((null ^ ~null)).to eq(universe)
      expect((single ^ ~single)).to eq(universe)
      expect((subset ^ ~subset)).to eq(universe)
      expect((universe ^ ~universe)).to eq(universe)
    end

    property("A ⊖ ¬A = U") do
      mksubset(universe)
    end.check do |a|
      expect((a ^ ~a)).to eq(universe)
    end

    specify "A ∖ ¬A = A" do
      expect((null - ~null)).to eq(null)
      expect((single - ~single)).to eq(single)
      expect((subset - ~subset)).to eq(subset)
      expect((universe - ~universe)).to eq(universe)
    end

    property("A ∖ ¬A = A") do
      mksubset(universe)
    end.check do |a|
      expect((a - ~a)).to eq(a)
    end

    specify "x ∉ ¬A, for all x ∉ U" do
      expect((~null)).to_not include("A")
      expect((~single)).to_not include("A")
      expect((~subset)).to_not include("A")
      expect((~universe)).to_not include("A")
    end

    property("x ∈ ¬A, for all x ∈ U and x ∉ A") do
      mksubset(universe)
    end.check do |a|
      (~a).each{|e| expect(a).to_not include(e) }
    end

    property("x ∉ ¬A, for all x ∈ U and x ∈ A") do
      mksubset(universe)
    end.check do |a|
      a.each{|e| expect(~a).to_not include(e) }
    end

    specify "¬U = ∅" do
      expect((~universe)).to eq(null)
    end

    specify "¬∅ = U" do
      expect((~null)).to eq(universe)
    end

    # Identity
    specify "¬(¬A) = A" do
      expect(~(~null)).to eq(null)
      expect(~(~single)).to eq(single)
      expect(~(~subset)).to eq(subset)
      expect(~(~universe)).to eq(universe)
    end

    property("¬(¬A) = A") do
      mksubset(universe)
    end.check do |a|
      expect((~(~a))).to eq(a)
    end

    # De Morgan's Laws
    property("¬(A ∪ B) = ¬A ∩ ¬B") do
      [mksubset(universe), mksubset(universe)]
    end.check do |a, b|
      expect(~(a | b)).to eq(~a & ~b)
    end

    property("¬(A ∩ B) = ¬A ∪ ¬B") do
      [mksubset(universe), mksubset(universe)]
    end.check do |a, b|
      expect(~(a & b)).to eq(~a | ~b)
    end

    # Uniqueness of Complements
    property("B = ¬A, given A ∪ B = U and A ∩ B = ∅") do
      # Create a smaller universe, because the chances of choosing
      # two random subsets from 2**26 possible, that happen to be
      # disjoint is very small.
      universe = Cantor.absolute(%w(a b c d e f))

      a = mksubset(universe)
      b = mksubset(universe)

      guard(a | b == universe)
      guard(a & b == null)

      [a, b]
    end.check(2, 500) do |a, b|
      expect(b).to eq(~a)
    end
  end

  describe "#union(other)" do
    property("x ∈ A ∪ B, for all x ∈ A") do
      a = mksubset(universe)
      b = mksubset(universe)
      [a, b, (a | b)]
    end.check do |a, b, union|
      a.each{|x| expect(union).to include(x) }
    end

    property("x ∈ A ∪ B, for all x ∈ B") do
      a = mksubset(universe)
      b = mksubset(universe)
      [a, b, (a | b)]
    end.check do |a, b, union|
      b.each{|x| expect(union).to include(x) }
    end

    property("x ∉ A ∪ B, for all x ∉ A and x ∉ B") do
      a = mksubset(universe)
      b = mksubset(universe)
      [a, b, (a | b)]
    end.check do |a, b, union|
      universe.each do |x|
        unless a.include?(x) or b.include?(x)
          expect(union).to_not include(x)
        end
      end
    end

    property("A ∪ B = A, given B ⊂ A") do
      # Create a smaller universe, because the chances of choosing
      # two random subsets from 2**26 possible, that happen to be
      # subsets of each other is very small.
      universe = Cantor.absolute(%w(a b c d e f))

      a = mksubset(universe)
      b = mksubset(universe)
      guard(b < a)

      [a, b]
    end.check do |a, b|
      expect(a | b).to eq(a)
    end

    property("A ∪ B = B, given B ⊃ A") do
      # Create a smaller universe, because the chances of choosing
      # two random subsets from 2**26 possible, that happen to be
      # subsets of each other is very small.
      universe = Cantor.absolute(%w(a b c d e f))

      a = mksubset(universe)
      b = mksubset(universe)
      guard(b > a)

      [a, b]
    end.check do |a, b|
      expect(a | b).to eq(b)
    end

    property("A ∪ B ⊇ A") do
      [mksubset(universe), mksubset(universe)]
    end.check do |a, b|
      expect(a | b).to be >= a
    end

    property("A ∪ B ⊇ B") do
      [mksubset(universe), mksubset(universe)]
    end.check do |a, b|
      expect(a | b).to be >= b
    end

    property("A ∪ B ⊃ A, given A ∩ B = ∅") do
      # Create a smaller universe, because the chances of choosing
      # two random subsets from 2**26 possible, that happen to be
      # disjoint is very small.
      universe = Cantor.absolute(%w(a b c d e f))

      a = mksubset(universe)
      b = mksubset(universe)
      guard(b & a == null)

      [a, b]
    end.check do |a, b|
      (a | b) > a
    end

    # Absorption
    property("A ∪ (A ∩ B) = A") do
      [mksubset(universe), mksubset(universe)]
    end.check do |a, b|
      expect(a | (a & b)).to eq(a)
    end

    # Idempotent
    specify "A ∪ A = A" do
      expect(null + null).to eq(null)
      expect(single + single).to eq(single)
      expect(subset + subset).to eq(subset)
      expect(universe + universe).to eq(universe)
    end

    # Domination
    specify "A ∪ U = U" do
      expect(null + universe).to eq(universe)
      expect(single + universe).to eq(universe)
      expect(subset + universe).to eq(universe)
      expect(universe + universe).to eq(universe)
    end

    # Complement
    specify "A ∪ ¬A = U" do
      expect(null | ~null).to eq(universe)
      expect(single | ~single).to eq(universe)
      expect(subset | ~subset).to eq(universe)
      expect(universe | ~universe).to eq(universe)
    end

    # Identity
    specify "A ∪ ∅ = A" do
      expect(null + null).to eq(null)
      expect(single + null).to eq(single)
      expect(subset + null).to eq(subset)
      expect(universe + null).to eq(universe)
    end

    # Distributive
    property("A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)") do
      [mksubset(universe), mksubset(universe), mksubset(universe)]
    end.check do |a, b, c|
      expect(a | (b & c)).to eq((a | b) & (a | c))
    end

    # Commutative
    property("A ∪ B = B ∪ A") do
      [mksubset(universe), mksubset(universe)]
    end.check do |a, b|
      expect(a | b).to eq(b | a)
    end

    # Associative
    property("(A ∪ B) ∪ C = A ∪ (B ∪ C)") do
      [mksubset(universe), mksubset(universe), mksubset(universe)]
    end.check do |a, b, c|
      expect((a | b) | c).to eq(a | (b | c))
    end

    context "if B is a RelativeSet" do
      context "and B ⊆ U" do
        property("then A ∪ B = A ∪ Cantor.absolute(B, U)") do
          [mksubset(universe), mksubset(universe)]
        end.check do |a, b|
          r = Cantor.build(b.to_a)

          expect(a | b).to eq(a | r)
          expect(a | r).to eq(a | b)
          expect(a | r).to be_a(Cantor::AbsoluteSet)
        end
      end

      context "and B ⊈ U" do
        property("then A ∪ B raises an error") do
          a = mksubset(universe)
          b = mksubset(Cantor.absolute(universe.to_a + universe.to_a.map(&:upcase)))
          [a, b]
        end.check do |a, b|
          r = Cantor.build(b.to_a)

          expect(lambda { a | r }).to \
            raise_error(/universe does not contain/)
        end
      end
    end

    context "if B is a RelativeComplement" do
      context "and ¬B ⊆ U" do
        property("then A ∪ B = B ∪ A") do
          a = mksubset(universe)
          b = mksubset(universe)

          [a, Cantor.complement(b.to_a)]
        end.check do |a, b|
          expect(a | b).to eq(b | a)
          expect(a | b).to be_a(Cantor::RelativeComplement)
        end
      end

      context "and ¬B ⊈ U" do
        property("then A ∪ B = B ∪ A") do
          a = mksubset(universe)
          b = mksubset(Cantor.absolute(universe.to_a + universe.to_a.map(&:upcase)))

          [a, Cantor.complement(b.to_a)]
        end.check do |a, b|
          expect(a | b).to eq(b | a)
          expect(a | b).to be_a(Cantor::RelativeComplement)
        end
      end
    end

    context "if B is an Array" do
      context "and B ⊆ U" do
        property("then A ∪ B = A ∪ Cantor.absolute(B, U)") do
          [mksubset(universe), mksubset(universe)]
        end.check do |a, b|
          r = b.to_a

          expect(a | b).to eq(a | r)
          expect(a | r).to eq(a | b)
          expect(a | r).to be_a(Cantor::AbsoluteSet)
        end
      end

      context "and B ⊈ U" do
        property("then A ∪ B raises an error") do
          a = mksubset(universe)
          b = mksubset(Cantor.absolute(universe.to_a + universe.to_a.map(&:upcase)))
          [a, b]
        end.check do |a, b|
          r = b.to_a

          expect(lambda { a | r }).to \
            raise_error(/universe does not contain/)
        end
      end
    end
  end

  describe "#intersection(other)" do
    property("x ∈ A ∩ B, for all x ∈ A and x ∈ B") do
      a = mksubset(universe)
      b = mksubset(universe)
      [a, b, (a & b)]
    end.check do |a, b, intersection|
      a.each do |x|
        if b.include?(x)
          expect(intersection).to include(x)
        end
      end
    end

    property("x ∉ A ∩ B, for all x ∉ A") do
      a = mksubset(universe)
      b = mksubset(universe)
      [a, b, (a & b)]
    end.check do |a, b, intersection|
      universe.each do |x|
        unless a.include?(x)
          expect(intersection).to_not include(x)
        end
      end
    end

    property("x ∉ A ∩ B, for all x ∉ B") do
      a = mksubset(universe)
      b = mksubset(universe)
      [a, b, (a & b)]
    end.check do |a, b, intersection|
      universe.each do |x|
        unless b.include?(x)
          expect(intersection).to_not include(x)
        end
      end
    end

    specify "A ∩ U = A" do
      expect(null & universe).to eq(null)
      expect(single & universe).to eq(single)
      expect(subset & universe).to eq(subset)
      expect(universe & universe).to eq(universe)
    end

    property("A ∩ B = A, given B ⊇ A") do
      # Create a smaller universe, because the chances of choosing
      # two random subsets from 2**26 possible, that happen to be
      # subsets of each other is very small.
      universe = Cantor.absolute(%w(a b c d e f))

      a = mksubset(universe)
      b = mksubset(universe)
      guard(b >= a)

      [a, b]
    end.check do |a, b|
      expect(a & b).to eq(a)
    end

    property("A ∩ B = B, given B ⊆ A") do
      # Create a smaller universe, because the chances of choosing
      # two random subsets from 2**26 possible, that happen to be
      # subsets of each other is very small.
      universe = Cantor.absolute(%w(a b c d e f))

      a = mksubset(universe)
      b = mksubset(universe)
      guard(b <= a)

      [a, b]
    end.check do |a, b|
      expect(a & b).to eq(b)
    end

    # Absorption
    property("A ∩ (A ∪ B) = A") do
      [mksubset(universe), mksubset(universe)]
    end.check do |a, b|
      expect(a & (a | b)).to eq(a)
    end

    # Idempotent
    specify "A ∩ A = A" do
      expect(null & null).to eq(null)
      expect(single & single).to eq(single)
      expect(subset & subset).to eq(subset)
      expect(universe & universe).to eq(universe)
    end

    # Domination
    specify "A ∩ ∅ = ∅" do
      expect(null & null).to eq(null)
      expect(single & null).to eq(null)
      expect(subset & null).to eq(null)
      expect(universe & null).to eq(null)
    end

    # Complement
    specify "A ∩ ¬A = ∅" do
      expect(null & ~null).to eq(null)
      expect(single & ~single).to eq(null)
      expect(subset & ~subset).to eq(null)
      expect(universe & ~universe).to eq(null)
    end

    # Distributive
    property("A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)") do
      [mksubset(universe), mksubset(universe), mksubset(universe)]
    end.check do |a, b, c|
      expect(a & (b | c)).to eq((a & b) | (a & c))
    end

    # Commutative
    property("A ∩ B = B ∩ A") do
      [mksubset(universe), mksubset(universe)]
    end.check do |a, b|
      expect(a & b).to eq(b & a)
    end

    # Associative
    property("(A ∩ B) ∩ C = A ∩ (B ∩ C)") do
      [mksubset(universe), mksubset(universe), mksubset(universe)]
    end.check do |a, b, c|
      expect((a & b) & c).to eq(a & (b & c))
    end

    context "if B is a RelativeSet" do
      context "and B ⊆ U" do
        property("then A ∩ B = A ∩ Cantor.absolute(B, U)") do
          [mksubset(universe), mksubset(universe)]
        end.check do |a, b|
          r = Cantor.build(b.to_a)

          expect(a & b).to eq(a & r)
          expect(a & r).to eq(a & b)
          expect(a & r).to be_a(Cantor::AbsoluteSet)
        end
      end

      context "and B ⊈ U" do
        property("then A ∩ B = A ∩ Cantor.absolute(B ∩ U, U)") do
          a = mksubset(universe)
          b = mksubset(Cantor.absolute(universe.to_a + universe.to_a.map(&:upcase)))
          [a, b]
        end.check do |a, b|
          r = Cantor.build(b.to_a)                # B
          b = universe.select{|x| b.include?(x) } # B ∩ U

          expect(a & b).to eq(a & r)
          expect(a & r).to eq(a & b)
          expect(a & r).to be_a(Cantor::AbsoluteSet)
        end
      end
    end

    context "if B is a RelativeComplement" do
      context "and ¬B ⊆ U" do
        property("then A ∩ B = B ∩ A") do
          a = mksubset(universe)
          b = mksubset(universe)

          [a, Cantor.complement(b.to_a)]
        end.check do |a, b|
          expect(a & b).to eq(b & a)
          expect(a & b).to be_a(Cantor::AbsoluteSet)
        end
      end

      context "and ¬B ⊈ U" do
        property("then A ∩ B = B ∩ A") do
          a = mksubset(universe)
          b = mksubset(Cantor.absolute(universe.to_a + universe.to_a.map(&:upcase)))

          [a, Cantor.complement(b.to_a)]
        end.check do |a, b|
          expect(a & b).to eq(b & a)
          expect(a & b).to be_a(Cantor::AbsoluteSet)
        end
      end
    end

    context "if B is an Array" do
      context "and B ⊆ U" do
        property("then A ∩ B = A ∩ Cantor.absolute(B, U)") do
          [mksubset(universe), mksubset(universe)]
        end.check do |a, b|
          r = b.to_a

          expect(a & b).to eq(a & r)
          expect(a & r).to eq(a & b)
          expect(a & r).to be_a(Cantor::AbsoluteSet)
        end
      end

      context "and B ⊈ U" do
        property("then A ∩ B = A ∩ Cantor.absolute(B ∩ U, U)") do
          a = mksubset(universe)
          b = mksubset(Cantor.absolute(universe.to_a + universe.to_a.map(&:upcase)))
          [a, b]
        end.check do |a, b|
          r = b.to_a                              # B
          b = universe.select{|x| b.include?(x) } # B ∩ U

          expect(a & b).to eq(a & r)
          expect(a & r).to eq(a & b)
          expect(a & r).to be_a(Cantor::AbsoluteSet)
        end
      end
    end
  end

  describe "#difference(other)" do
    property("x ∈ A ∖ B, for all x ∈ A and x ∉ B") do
      a = mksubset(universe)
      b = mksubset(universe)
      [a, b, (a - b)]
    end.check do |a, b, difference|
      a.each do |x|
        unless b.include?(x)
          expect(difference).to include(x)
        end
      end
    end

    property("x ∉ A ∖ B, for all x ∉ A") do
      a = mksubset(universe)
      b = mksubset(universe)
      [a, b, (a - b)]
    end.check do |a, b, difference|
      universe.each do |x|
        unless a.include?(x)
          expect(difference).to_not include(x)
        end
      end
    end

    property("x ∉ A ∖ B, for all x ∈ B") do
      a = mksubset(universe)
      b = mksubset(universe)
      [a, b, (a - b)]
    end.check do |a, b, difference|
      b.each do |x|
        expect(difference.include?(x)).to be_false
      end
    end

    specify "U ∖ A = ¬A" do
      expect(universe - null).to eq(~null)
      expect(universe - single).to eq(~single)
      expect(universe - subset).to eq(~subset)
      expect(universe - universe).to eq(~universe)
    end

    specify "∅ ∖ A = ∅" do
      expect(null - null).to eq(null)
      expect(null - single).to eq(null)
      expect(null - subset).to eq(null)
      expect(null - universe).to eq(null)
    end

    specify "A ∖ A = ∅" do
      expect(null - null).to eq(null)
      expect(single - single).to eq(null)
      expect(subset - subset).to eq(null)
      expect(universe - universe).to eq(null)
    end

    specify "A ∖ ∅ = A" do
      expect(null - null).to eq(null)
      expect(single - null).to eq(single)
      expect(subset - null).to eq(subset)
      expect(universe - null).to eq(universe)
    end

    specify "A ∖ U = ∅" do
      expect(null - universe).to eq(null)
      expect(single - universe).to eq(null)
      expect(subset - universe).to eq(null)
      expect(universe - universe).to eq(null)
    end

    property("A ∖ B = A, given A ∩ B = ∅")

    property("A ∖ B ⊂ A, given A ∩ B ≠ ∅") do
      a = mksubset(universe)
      b = mksubset(universe)
      guard(a & b != null)

      [a, b]
    end.check do |a, b|
      expect(a - b).to be < a
    end

    property("A ∖ B ≠ B ∖ A, given A ≠ B") do
      a = mksubset(universe)
      b = mksubset(universe)
      guard(a != b)

      [a, b]
    end.check do |a, b|
      expect(a - b).to eq(b - a)
    end

    property("C ∖ (A ∩ B) = (C ∖ A) ∪ (C ∖ B)") do
      [mksubset(universe), mksubset(universe), mksubset(universe)]
    end.check do |a, b, c|
      expect(c - (a & b)).to eq((c - a) | (c - b))
    end

    property("C ∖ (A ∪ B) = (C ∖ A) ∩ (C ∖ B)") do
      [mksubset(universe), mksubset(universe), mksubset(universe)]
    end.check do |a, b, c|
      expect(c - (a | b)).to eq((c - a) & (c - b))
    end

    property("C ∖ (B ∖ A) = (A ∩ C) ∪ (C ∖ B)") do
      [mksubset(universe), mksubset(universe), mksubset(universe)]
    end.check do |a, b, c|
      expect(c - (b - a)).to eq((a & c) | (c - b))
    end

  # property("(B ∖ A) ∩ C = (B ∩ C) ∖ A = B ∩ (C ∖ A)") do
  #   [mksubset(universe), mksubset(universe), mksubset(universe)]
  # end.check do |a, b, c|
  # end

    property("(B ∖ A) ∪ C = (B ∪ C) ∖ (A ∖ C)") do
      [mksubset(universe), mksubset(universe), mksubset(universe)]
    end.check do |a, b, c|
      expect((b - a) | c).to eq((b | c) - (a - c))
    end

    property("B ∖ A = ¬A ∩ B") do
      [mksubset(universe), mksubset(universe)]
    end.check do |a, b|
      expect(b - a).to eq(~a & b)
    end

    property("¬(B ∖ A) = A ∪ ¬B") do
      [mksubset(universe), mksubset(universe)]
    end.check do |a, b|
      expect(~(b - a)).to eq(a | ~b)
    end

    context "if B is a RelativeSet" do
      context "and B ⊆ U" do
        property("then A ∖ B = A ∖ Cantor.absolute(B, U)") do
          [mksubset(universe), mksubset(universe)]
        end.check do |a, b|
          r = Cantor.build(b.to_a)

          expect(a - b).to eq(a - r)
          expect(a - r).to eq(a - b)
          expect(a - r).to be_a(Cantor::AbsoluteSet)
        end
      end

      context "and B ⊈ U" do
        property("then A ∖ B = A ∖ Cantor.absolute(B ∩ U, U)") do
          a = mksubset(universe)
          b = mksubset(Cantor.absolute(universe.to_a + universe.to_a.map(&:upcase)))
          [a, b]
        end.check do |a, b|
          r = Cantor.build(b.to_a)                # B
          b = universe.select{|x| b.include?(x) } # B ∩ U

          expect(a - b).to eq(a - r)
          expect(a - r).to eq(a - b)
          expect(a - r).to be_a(Cantor::AbsoluteSet)
        end
      end
    end

    context "if B is a RelativeComplement" do
      context "and ¬B ⊆ U" do
        property("then A ∖ B = A ∩ ¬B") do
          a = mksubset(universe)
          b = mksubset(universe)

          [a, Cantor.complement(b.to_a)]
        end.check do |a, b|
          expect(a - b).to eq(a & ~b)
          expect(a - b).to be_a(Cantor::AbsoluteSet)
        end
      end

      context "and ¬B ⊈ U" do
        property("then A ∖ B = A ∩ ¬B") do
          a = mksubset(universe)
          b = mksubset(Cantor.absolute(universe.to_a + universe.to_a.map(&:upcase)))

          [a, Cantor.complement(b.to_a)]
        end.check do |a, b|
          expect(a - b).to eq(a & ~b)
          expect(a - b).to be_a(Cantor::AbsoluteSet)
        end
      end
    end

    context "if B is an Array" do
      context "and B ⊆ U" do
        property("then A ∖ B = A ∖ Cantor.absolute(B, U)") do
          [mksubset(universe), mksubset(universe)]
        end.check do |a, b|
          r = b.to_a

          expect(a - b).to eq(a - r)
          expect(a - r).to eq(a - b)
          expect(a - r).to be_a(Cantor::AbsoluteSet)
        end
      end

      context "and B ⊈ U" do
        property("then A ∖ B = A ∖ Cantor.absolute(B ∩ U, U)") do
          a = mksubset(universe)
          b = mksubset(Cantor.absolute(universe.to_a + universe.to_a.map(&:upcase)))
          [a, b]
        end.check do |a, b|
          r = b.to_a                              # B
          b = universe.select{|x| b.include?(x) } # B ∩ U

          expect(a - b).to eq(a - r)
          expect(a - r).to eq(a - b)
          expect(a - r).to be_a(Cantor::AbsoluteSet)
        end
      end
    end
  end

  describe "#symmetric_difference(other)" do
    specify "A ⊖ A = ∅" do
      expect(null ^ null).to eq(null)
      expect(single ^ single).to eq(null)
      expect(subset ^ subset).to eq(null)
      expect(universe ^ universe).to eq(null)
    end

    specify "A ⊖ U = ¬A" do
      expect(null ^ universe).to eq(~null)
      expect(single ^ universe).to eq(~single)
      expect(subset ^ universe).to eq(~subset)
      expect(universe ^ universe).to eq(~universe)
    end

    specify "A ⊖ ∅ = A" do
      expect(null ^ null).to eq(null)
      expect(single ^ null).to eq(single)
      expect(subset ^ null).to eq(subset)
      expect(universe ^ null).to eq(universe)
    end

    property("A ⊖ B = (A ∖ B) ∪ (B ∖ A)") do
      [mksubset(universe), mksubset(universe)]
    end.check do |a, b|
      expect(a ^ b).to eq((a - b) | (b - a))
    end

    property("A ⊖ B = (A ∪ B) ∖ (A ∩ B)") do
      [mksubset(universe), mksubset(universe)]
    end.check do |a, b|
      expect(a ^ b).to eq((a | b) - (a & b))
    end

    property("A ⊖ B = B ⊖ A") do
      [mksubset(universe), mksubset(universe)]
    end.check do |a, b|
      expect(a ^ b).to eq(b ^ a)
    end

    property("(A ⊖ B) ⊖ C = A ⊖ (B ⊖ C)") do
      [mksubset(universe), mksubset(universe), mksubset(universe)]
    end.check do |a, b, c|
      expect((a ^ b) ^ c).to eq(a ^ (b ^ c))
    end

    property("(A ⊖ B) ⊖ (B ⊖ C) = A ⊖ C") do
      [mksubset(universe), mksubset(universe), mksubset(universe)]
    end.check do |a, b, c|
      expect((a ^ b) ^ (b ^ c)).to eq(a ^ c)
    end

    property("A ∩ (B ⊖ C) = (A ∩ B) ⊖ (A ∩ C)") do
      [mksubset(universe), mksubset(universe), mksubset(universe)]
    end.check do |a, b, c|
      expect(a & (b ^ c)).to eq((a & b) ^ (a & c))
    end

    context "if B is a RelativeSet" do
      context "and B ⊆ U" do
        property("then A ⊖ B = A ⊖ Cantor.absolute(B, U)") do
          [mksubset(universe), mksubset(universe)]
        end.check do |a, b|
          r = Cantor.build(b.to_a)

          expect(a ^ b).to eq(a ^ r)
          expect(a ^ r).to eq(a ^ b)
          expect(a ^ r).to be_a(Cantor::AbsoluteSet)
        end
      end

      context "and B ⊈ U" do
        property("then A ⊖ B raises an error") do
          a = mksubset(universe)
          b = mksubset(Cantor.absolute(universe.to_a + universe.to_a.map(&:upcase)))
          [a, b]
        end.check do |a, b|
          r = Cantor.build(b.to_a)

          expect(lambda { a ^ r }).to \
            raise_error(/universe does not contain/)
        end
      end
    end

    context "if B is a RelativeComplement" do
      context "and ¬B ⊆ U" do
        property("then A ⊖ B = B ⊖ A") do
          a = mksubset(universe)
          b = mksubset(universe)

          [a, Cantor.complement(b.to_a)]
        end.check do |a, b|
          expect(a ^ b).to eq(b ^ a)
          expect(a ^ b).to be_a(Cantor::AbsoluteSet)
        end
      end

      context "and ¬B ⊈ U" do
        property("then A ⊖ B = B ⊖ A") do
          a = mksubset(universe)
          b = mksubset(Cantor.absolute(universe.to_a + universe.to_a.map(&:upcase)))

          [a, Cantor.complement(b.to_a)]
        end.check do |a, b|
          expect(a ^ b).to eq(b ^ a)
          expect(a ^ b).to be_a(Cantor::AbsoluteSet)
        end
      end
    end

    context "if B is an Array" do
      context "and B ⊆ U" do
        property("then A ⊖ B = A ⊖ Cantor.absolute(B, U)") do
          [mksubset(universe), mksubset(universe)]
        end.check do |a, b|
          r = b.to_a

          expect(a ^ b).to eq(a ^ r)
          expect(a ^ r).to eq(a ^ b)
          expect(a ^ r).to be_a(Cantor::AbsoluteSet)
        end
      end

      context "and B ⊈ U" do
        property("then A ⊖ B raises an error") do
          a = mksubset(universe)
          b = mksubset(Cantor.absolute(universe.to_a + universe.to_a.map(&:upcase)))
          [a, b]
        end.check do |a, b|
          r = b.to_a

          expect(lambda { a ^ r }).to \
            raise_error(/universe does not contain/)
        end
      end
    end
  end

  describe "#subset?(other)" do
    # Reflexivity
    specify "A ⊆ A" do
      expect(null).to be <= null
      expect(single).to be <= single
      expect(subset).to be <= subset
      expect(universe).to be <= universe
    end

    # Antisymmetry
    property("A ⊆ B and B ⊆ A, given A = B") do
      universe = Cantor.absolute(%w(a b c d e f))

      a = mksubset(universe)
      b = mksubset(universe)
      guard(a == b)

      [a, b]
    end.check(5, 200) do |a, b|
      expect(a).to be <= b
      expect(b).to be <= a
    end

    property("A = B, given A ⊆ B and B ⊆ A") do
      universe = Cantor.absolute(%w(a b c d e f))

      a = mksubset(universe)
      b = mksubset(universe)
      guard(a <= b)
      guard(b <= a)

      [a, b]
    end.check(5, 200) do |a, b|
      expect(a).to eq(b)
    end

    # Transitivity
    property("A ⊆ C, given A ⊆ B and B ⊆ C") do
      universe = Cantor.absolute(%w(a b c d e f))

      a = mksubset(universe)
      b = mksubset(universe)
      c = mksubset(universe)
      guard(a <= b)
      guard(b <= c)

      [a, b, c]
    end.check(5, 200) do |a, b, c|
      expect(a).to be <= c
    end

    # Existence of a Least Element
    specify "∅ ⊆ A" do
      expect(null).to be <= null
      expect(null).to be <= single
      expect(null).to be <= subset
      expect(null).to be <= universe
    end

    # Existence of a Greatest Element
    specify "A ⊆ U" do
      expect(null).to be <= universe
      expect(single).to be <= universe
      expect(subset).to be <= universe
      expect(universe).to be <= universe
    end

    # Existence of Joins
    property("A ⊆ A ∪ B") do
      [mksubset(universe), mksubset(universe)]
    end.check do |a, b|
      expect(a).to be <= (a | b)
    end

    # Existence of meets
    property("A ∪ B ⊇ C, given C ⊆ A and C ⊆ B") do
      universe = Cantor.absolute(%w(a b c d e f))

      a = mksubset(universe)
      b = mksubset(universe)
      c = mksubset(universe)
      guard(c <= a)
      guard(c <= b)

      [a, b, c]
    end.check(5, 200) do |a, b, c|
      expect(a | b).to be >= c
    end

    # Equivalent Statements
    property("A ⊆ B => ...") do
      [mksubset(universe), mksubset(universe)]
    end.check do |a, b|
      if a <= b
        expect(a & b).to eq(a)
        expect(a | b).to eq(b)
        expect(a - b).to eq(null)
        expect(~b).to be <= (~a)
      end
    end

    # Equivalent Statements
    property("A ∩ B = A => ...") do
      [mksubset(universe), mksubset(universe)]
    end.check do |a, b|
      if (a & b) == a
        expect(a).to be <= b
        expect(a | b).to eq(b)
        expect(a - b).to eq(null)
        expect(~b).to be <= (~a)
      end
    end

    # Equivalent Statements
    property("A ∪ B = B => ...") do
      [mksubset(universe), mksubset(universe)]
    end.check do |a, b|
      if (a | b) == b
        expect(a).to be <= b
        expect(a & b).to eq(a)
        expect(a - b).to eq(null)
        expect(~b).to be <= (~a)
      end
    end

    # Equivalent Statements
    property("A ∖ B = ∅ => ...") do
      [mksubset(universe), mksubset(universe)]
    end.check do |a, b|
      if (a - b) == null
        expect(a).to be <= b
        expect(a & b).to eq(a)
        expect(a | b).to eq(b)
        expect(~b).to be <= (~a)
      end
    end

    # Equivalent Statements
    property("¬B ⊆ ¬A => ...") do
      [mksubset(universe), mksubset(universe)]
    end.check do |a, b|
      if (~b) <= (~a)
        expect(a).to be <= b
        expect(a & b).to eq(a)
        expect(a | b).to eq(b)
        expect(a - b).to eq(null)
      end
    end

    context "if B is a RelativeSet" do
      context "and B ⊆ U" do
        property("then A ⊆ B = A ⊆ Cantor.absolute(B, U)") do
          [mksubset(universe), mksubset(universe)]
        end.check do |a, b|
          r = Cantor.build(b.to_a)
          expect(a <= b).to eq(a <= r)
        end
      end

      context "and B ⊈ U" do
        property("then A ⊈ B = A ⊆ Cantor.absolute(B ∩ U, U)") do
          a = mksubset(universe)
          b = mksubset(Cantor.absolute(universe.to_a + universe.to_a.map(&:upcase)))
          [a, b]
        end.check do |a, b|
          r = Cantor.build(b.to_a)                # B
          b = universe.select{|x| b.include?(x) } # B ∩ U
          expect(a <= b).to eq(a <= r)
        end
      end
    end

    context "if B is a RelativeComplement(C)" do
      context "and C ⊆ U" do
        property("then A ⊆ ¬C ≡ A ∩ C = ∅") do
          [mksubset(universe), mksubset(universe)]
        end.check do |a, c|
          b = Cantor.complement(c.to_a)
          expect(a <= b).to eq((a & c) == null)
        end
      end

      context "and C ⊈ U" do
        property("then A ⊆ ¬C ≡ A ∩ C = ∅") do
          a = mksubset(universe)
          c = mksubset(Cantor.absolute(universe.to_a + universe.to_a.map(&:upcase)))
          [a, c]
        end.check do |a, c|
          b = Cantor.complement(c.to_a)
          expect(a <= b).to eq((a & c) == null)
        end
      end
    end

    context "when B is an Array" do
      context "and B ⊆ U" do
        property("then A ⊆ B = A ⊆ Cantor.absolute(B, U)") do
          [mksubset(universe), mksubset(universe)]
        end.check do |a, b|
          r = b.to_a
          expect(a <= b).to eq(a <= r)
        end
      end

      context "and B ⊈ U" do
        property("then A ⊆ B = A ⊆ Cantor.absolute(B ∩ U, U)") do
          a = mksubset(universe)
          b = mksubset(Cantor.absolute(universe.to_a + universe.to_a.map(&:upcase)))
          [a, b]
        end.check do |a, b|
          r = b.to_a                              # B
          b = universe.select{|x| b.include?(x) } # B ∩ U

          expect(a <= b).to eq(a <= r)
        end
      end
    end
  end

  describe "#==(other)" do
    # Reflexive
    specify "A = A" do
      expect(null).to eq(null)
      expect(single).to eq(single)
      expect(subset).to eq(subset)
      expect(universe).to eq(universe)
    end

    # Symmetric
    property("if A = B then B = A") do
      universe = Cantor.absolute(%w(a b c d e f))
      [mksubset(universe), mksubset(universe)]
    end.check do |a, b|
      if a == b
        expect(b).to eq(a)
      end
    end

    # Transitive
    property("if A = B and B = C then A = C") do
      universe = Cantor.absolute(%w(a b c d e f))
      [mksubset(universe), mksubset(universe), mksubset(universe)]
    end.check do |a, b, c|
      if a == b and b == c
        expect(a).to eq(c)
      end
    end

    context "if B is a RelativeSet" do
      context "and B ⊆ U" do
        property("then A = B ≡ A = Cantor.absolute(B, U)") do
          [mksubset(universe), mksubset(universe)]
        end.check do |a, b|
          r = Cantor.build(b.to_a)
          expect(a == b).to eq(a == r)
        end
      end

      context "and B ⊈ U" do
        property("then A = B ≡ A = Cantor.absolute(B ∩ U, U)") do
          a = mksubset(universe)
          b = mksubset(Cantor.absolute(universe.to_a + universe.to_a.map(&:upcase)))
          [a, b]
        end.check do |a, b|
          r = Cantor.build(b.to_a)                # B
          b = universe.select{|x| b.include?(x) } # B ∩ U
          expect(a == b).to eq(a == r)
        end
      end
    end

    context "if B is a RelativeComplement" do
      context "and ¬B ⊆ U" do
        property("then A = B ≡ B = A") do
          a = mksubset(universe)
          b = mksubset(universe)

          [a, Cantor.complement(b.to_a)]
        end.check do |a, b|
          expect(a == b).to eq(b == a)
        end
      end

      context "and ¬B ⊈ U" do
        property("then A = B ≡ B = A") do
          a = mksubset(universe)
          b = mksubset(Cantor.absolute(universe.to_a + universe.to_a.map(&:upcase)))

          [a, Cantor.complement(b.to_a)]
        end.check do |a, b|
          expect(a == b).to eq(b == a)
        end
      end
    end

    context "if B is an Array" do
      context "and B ⊆ U" do
        property("then A = B ≡ A = Cantor.absolute(B, U)") do
          [mksubset(universe), mksubset(universe)]
        end.check do |a, b|
          r = b.to_a
          expect(a == b).to eq(a == r)
        end
      end

      context "and B ⊈ U" do
        property("then A = B ≡ A = Cantor.absolute(B ∩ U, U)") do
          a = mksubset(universe)
          b = mksubset(Cantor.absolute(universe.to_a + universe.to_a.map(&:upcase)))
          [a, b]
        end.check do |a, b|
          r = b.to_a                              # B
          b = universe.select{|x| b.include?(x) } # B ∩ U

          expect(a == b).to eq(a == r)
        end
      end
    end
  end

  describe "#replace(other)" do
    context "if B is an AbsoluteSet" do
      context "and B.universe = U" do
        property("then A.replace(B) = B") do
          [mksubset(universe), mksubset(universe)]
        end.check do |a, b|
          expect(a.replace(b)).to eq(b)
        end
      end

      context "and B.universe ≠ U" do
        property("then A.replace(B) = B") do
          a = mksubset(universe)
          b = mksubset(Cantor.absolute(universe.to_a + universe.to_a.map(&:upcase)))
          [a, b]
        end.check do |a, b|
          expect(a.replace(b)).to eq(b)
        end
      end
    end

    context "if B is a RelativeSet" do
      property("then A.replace(B) = B") do
        a = mksubset(universe)
        b = mksubset(Cantor.absolute(universe.to_a + universe.to_a.map(&:upcase)))
        [a, Cantor.build(b.to_a)]
      end.check do |a, b|
        expect(a.replace(b)).to eq(b)
      end
    end

    context "if B is a RelativeComplement" do
      property("then A.replace(B) = B") do
        a = mksubset(universe)
        b = mksubset(Cantor.absolute(universe.to_a + universe.to_a.map(&:upcase)))
        [a, Cantor.complement(b.to_a)]
      end.check do |a, b|
        expect(a.replace(b)).to eq(b)
      end
    end

    context "if B is an Array" do
      context "and B ⊆ U" do
        property("then A.replace(B) ≡ Cantor.absolute(B, U)") do
          [mksubset(universe), mksubset(universe)]
        end.check do |a, b|
          expect(a.replace(b.to_a)).to eq(b)
        end
      end

      context "and B ⊈ U" do
        property("then A.replace(B) raises an error") do
          a = mksubset(universe)
          b = mksubset(universe)
          c = mksubset(universe)
          guard(!c.empty?)

          [a, (b.to_a | c.to_a.map(&:upcase))]
        end.check do |a, b|
          expect(lambda { a.replace(b) }).to \
            raise_error(/universe does not contain/)
        end
      end
    end
  end

end
