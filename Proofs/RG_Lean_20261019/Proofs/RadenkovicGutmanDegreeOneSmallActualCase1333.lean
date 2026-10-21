/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1333 : Family 9 := level9.get ⟨89,by decide⟩
def sourceMap1333 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,5,6,3,4] (sourceLabel 9 0 0 v)
def fusedMap1333 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap1333_checked : acceptsGraphIso
    (source (graph core1333) (root 9) 0 0) DegreeOneSmallSpectrum438.graph sourceMap1333=true := by decide +kernel
theorem fusedMap1333_checked : acceptsGraphIso
    (fused (graph core1333) (root 9) 0 0) DegreeOneSmallSpectrum557.graph fusedMap1333=true := by decide +kernel
theorem certified1333 : Certified (graph core1333) (root 9) 0 0 :=
  of_native_maps core1333 DegreeOneSmallSpectrum438.graph DegreeOneSmallSpectrum557.graph
    sourceMap1333 fusedMap1333 sourceMap1333_checked fusedMap1333_checked
    DegreeOneSmallComparisons.comparison1333
#print axioms sourceMap1333_checked
#print axioms fusedMap1333_checked
#print axioms certified1333
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
