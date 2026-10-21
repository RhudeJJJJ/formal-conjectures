/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2139 : Family 10 := level10.get ⟨585,by decide⟩
def sourceMap2139 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap2139 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2139_checked : acceptsGraphIso
    (source (graph core2139) (root 10) 0 0) DegreeOneSmallSpectrum1757.graph sourceMap2139=true := by decide +kernel
theorem fusedMap2139_checked : acceptsGraphIso
    (fused (graph core2139) (root 10) 0 0) DegreeOneSmallSpectrum1132.graph fusedMap2139=true := by decide +kernel
theorem certified2139 : Certified (graph core2139) (root 10) 0 0 :=
  of_native_maps core2139 DegreeOneSmallSpectrum1757.graph DegreeOneSmallSpectrum1132.graph
    sourceMap2139 fusedMap2139 sourceMap2139_checked fusedMap2139_checked
    DegreeOneSmallComparisons.comparison2139
#print axioms sourceMap2139_checked
#print axioms fusedMap2139_checked
#print axioms certified2139
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
