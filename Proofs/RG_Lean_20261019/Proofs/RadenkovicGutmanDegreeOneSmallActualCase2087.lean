/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2087 : Family 10 := level10.get ⟨500,by decide⟩
def sourceMap2087 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap2087 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2087_checked : acceptsGraphIso
    (source (graph core2087) (root 10) 0 0) DegreeOneSmallSpectrum1548.graph sourceMap2087=true := by decide +kernel
theorem fusedMap2087_checked : acceptsGraphIso
    (fused (graph core2087) (root 10) 0 0) DegreeOneSmallSpectrum984.graph fusedMap2087=true := by decide +kernel
theorem certified2087 : Certified (graph core2087) (root 10) 0 0 :=
  of_native_maps core2087 DegreeOneSmallSpectrum1548.graph DegreeOneSmallSpectrum984.graph
    sourceMap2087 fusedMap2087 sourceMap2087_checked fusedMap2087_checked
    DegreeOneSmallComparisons.comparison2087
#print axioms sourceMap2087_checked
#print axioms fusedMap2087_checked
#print axioms certified2087
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
