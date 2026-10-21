/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2144 : Family 10 := level10.get ⟨593,by decide⟩
def sourceMap2144 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap2144 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2144_checked : acceptsGraphIso
    (source (graph core2144) (root 10) 0 0) DegreeOneSmallSpectrum1811.graph sourceMap2144=true := by decide +kernel
theorem fusedMap2144_checked : acceptsGraphIso
    (fused (graph core2144) (root 10) 0 0) DegreeOneSmallSpectrum1141.graph fusedMap2144=true := by decide +kernel
theorem certified2144 : Certified (graph core2144) (root 10) 0 0 :=
  of_native_maps core2144 DegreeOneSmallSpectrum1811.graph DegreeOneSmallSpectrum1141.graph
    sourceMap2144 fusedMap2144 sourceMap2144_checked fusedMap2144_checked
    DegreeOneSmallComparisons.comparison2144
#print axioms sourceMap2144_checked
#print axioms fusedMap2144_checked
#print axioms certified2144
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
