import Definitions.Def_RevenueManagement_competition

namespace RevenueManagement

theorem mnl_offer_set_equilibrium (A B : OfferFirm) (w0 : ℝ) (hw0 : 0 < w0) (hA : A.IsModel)
    (hB : B.IsModel) (hcase : (A.CaseI w0 ∧ B.CaseI w0) ∨ (A.CaseII w0 ∧ B.CaseII w0)) :
    ∃ k l, IsOfferEquilibrium A B w0 k l := by sorry

end RevenueManagement
