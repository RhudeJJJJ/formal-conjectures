/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2151 : Family 10 := level10.get ⟨605,by decide⟩
def sourceMap2151 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (sourceLabel 10 0 0 v)
def fusedMap2151 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2151_checked : acceptsGraphIso
    (source (graph core2151) (root 10) 0 0) DegreeOneSmallSpectrum1746.graph sourceMap2151=true := by decide +kernel
theorem fusedMap2151_checked : acceptsGraphIso
    (fused (graph core2151) (root 10) 0 0) DegreeOneSmallSpectrum1176.graph fusedMap2151=true := by decide +kernel
theorem certified2151 : Certified (graph core2151) (root 10) 0 0 :=
  of_native_maps core2151 DegreeOneSmallSpectrum1746.graph DegreeOneSmallSpectrum1176.graph
    sourceMap2151 fusedMap2151 sourceMap2151_checked fusedMap2151_checked
    DegreeOneSmallComparisons.comparison2151
#print axioms sourceMap2151_checked
#print axioms fusedMap2151_checked
#print axioms certified2151
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
