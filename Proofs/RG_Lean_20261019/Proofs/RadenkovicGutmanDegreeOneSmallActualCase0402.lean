/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0402 : Family 6 := level6.get ⟨22,by decide⟩
def sourceMap0402 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![1,0,4,5,6,7,8,2,3] (sourceLabel 6 0 0 v)
def fusedMap0402 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![6,0,1,2,3,4,5,7,8] (fusedLabel 6 0 0 v)
theorem sourceMap0402_checked : acceptsGraphIso
    (source (graph core0402) (root 6) 0 0) DegreeOneSmallSpectrum069.graph sourceMap0402=true := by decide +kernel
theorem fusedMap0402_checked : acceptsGraphIso
    (fused (graph core0402) (root 6) 0 0) DegreeOneSmallSpectrum043.graph fusedMap0402=true := by decide +kernel
theorem certified0402 : Certified (graph core0402) (root 6) 0 0 :=
  of_native_maps core0402 DegreeOneSmallSpectrum069.graph DegreeOneSmallSpectrum043.graph
    sourceMap0402 fusedMap0402 sourceMap0402_checked fusedMap0402_checked
    DegreeOneSmallComparisons.comparison0402
#print axioms sourceMap0402_checked
#print axioms fusedMap0402_checked
#print axioms certified0402
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
