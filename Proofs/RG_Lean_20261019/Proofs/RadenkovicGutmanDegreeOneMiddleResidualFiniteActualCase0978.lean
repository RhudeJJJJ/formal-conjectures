/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0978 : Family 10 := level10.get ⟨843,by decide⟩
def sourceMap0978 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0978 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0978_checked : acceptsGraphIso
    (source (graph core0978) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2276.graph sourceMap0978=true := by decide +kernel
theorem fusedMap0978_checked : acceptsGraphIso
    (fused (graph core0978) (root 10) 2 2) DegreeTwoThreeSpectrum5676.graph fusedMap0978=true := by decide +kernel
theorem certified0978 : Certified (graph core0978) (root 10) 2 2 :=
  of_native_maps core0978 DegreeOneMiddleResidualSpectrum2276.graph DegreeTwoThreeSpectrum5676.graph
    sourceMap0978 fusedMap0978 sourceMap0978_checked fusedMap0978_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0978
#print axioms sourceMap0978_checked
#print axioms fusedMap0978_checked
#print axioms certified0978
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
