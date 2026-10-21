/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2118 : Family 10 := level10.get ⟨548,by decide⟩
def sourceMap2118 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (sourceLabel 10 0 0 v)
def fusedMap2118 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2118_checked : acceptsGraphIso
    (source (graph core2118) (root 10) 0 0) DegreeOneSmallSpectrum1671.graph sourceMap2118=true := by decide +kernel
theorem fusedMap2118_checked : acceptsGraphIso
    (fused (graph core2118) (root 10) 0 0) DegreeOneSmallSpectrum1075.graph fusedMap2118=true := by decide +kernel
theorem certified2118 : Certified (graph core2118) (root 10) 0 0 :=
  of_native_maps core2118 DegreeOneSmallSpectrum1671.graph DegreeOneSmallSpectrum1075.graph
    sourceMap2118 fusedMap2118 sourceMap2118_checked fusedMap2118_checked
    DegreeOneSmallComparisons.comparison2118
#print axioms sourceMap2118_checked
#print axioms fusedMap2118_checked
#print axioms certified2118
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
