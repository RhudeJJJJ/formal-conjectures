/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2202 : Family 10 := level10.get ⟨714,by decide⟩
def sourceMap2202 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (sourceLabel 10 0 0 v)
def fusedMap2202 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2202_checked : acceptsGraphIso
    (source (graph core2202) (root 10) 0 0) DegreeOneSmallSpectrum1717.graph sourceMap2202=true := by decide +kernel
theorem fusedMap2202_checked : acceptsGraphIso
    (fused (graph core2202) (root 10) 0 0) DegreeOneSmallSpectrum1341.graph fusedMap2202=true := by decide +kernel
theorem certified2202 : Certified (graph core2202) (root 10) 0 0 :=
  of_native_maps core2202 DegreeOneSmallSpectrum1717.graph DegreeOneSmallSpectrum1341.graph
    sourceMap2202 fusedMap2202 sourceMap2202_checked fusedMap2202_checked
    DegreeOneSmallComparisons.comparison2202
#print axioms sourceMap2202_checked
#print axioms fusedMap2202_checked
#print axioms certified2202
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
