/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2112 : Family 10 := level10.get ⟨537,by decide⟩
def sourceMap2112 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,10,8,9] (sourceLabel 10 0 0 v)
def fusedMap2112 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2112_checked : acceptsGraphIso
    (source (graph core2112) (root 10) 0 0) DegreeOneSmallSpectrum1679.graph sourceMap2112=true := by decide +kernel
theorem fusedMap2112_checked : acceptsGraphIso
    (fused (graph core2112) (root 10) 0 0) DegreeOneSmallSpectrum1043.graph fusedMap2112=true := by decide +kernel
theorem certified2112 : Certified (graph core2112) (root 10) 0 0 :=
  of_native_maps core2112 DegreeOneSmallSpectrum1679.graph DegreeOneSmallSpectrum1043.graph
    sourceMap2112 fusedMap2112 sourceMap2112_checked fusedMap2112_checked
    DegreeOneSmallComparisons.comparison2112
#print axioms sourceMap2112_checked
#print axioms fusedMap2112_checked
#print axioms certified2112
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
