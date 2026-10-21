/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2126 : Family 10 := level10.get ⟨565,by decide⟩
def sourceMap2126 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap2126 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2126_checked : acceptsGraphIso
    (source (graph core2126) (root 10) 0 0) DegreeOneSmallSpectrum1747.graph sourceMap2126=true := by decide +kernel
theorem fusedMap2126_checked : acceptsGraphIso
    (fused (graph core2126) (root 10) 0 0) DegreeOneSmallSpectrum1091.graph fusedMap2126=true := by decide +kernel
theorem certified2126 : Certified (graph core2126) (root 10) 0 0 :=
  of_native_maps core2126 DegreeOneSmallSpectrum1747.graph DegreeOneSmallSpectrum1091.graph
    sourceMap2126 fusedMap2126 sourceMap2126_checked fusedMap2126_checked
    DegreeOneSmallComparisons.comparison2126
#print axioms sourceMap2126_checked
#print axioms fusedMap2126_checked
#print axioms certified2126
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
