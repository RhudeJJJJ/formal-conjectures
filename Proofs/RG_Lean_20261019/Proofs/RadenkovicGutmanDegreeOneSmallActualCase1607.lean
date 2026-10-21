/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1607 : Family 9 := level9.get ⟨346,by decide⟩
def sourceMap1607 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,5,0,1,2,3,4,9,10,11,7,8] (sourceLabel 9 0 0 v)
def fusedMap1607 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap1607_checked : acceptsGraphIso
    (source (graph core1607) (root 9) 0 0) DegreeOneSmallSpectrum661.graph sourceMap1607=true := by decide +kernel
theorem fusedMap1607_checked : acceptsGraphIso
    (fused (graph core1607) (root 9) 0 0) SmallGeFourSpectrum138.graph fusedMap1607=true := by decide +kernel
theorem certified1607 : Certified (graph core1607) (root 9) 0 0 :=
  of_native_maps core1607 DegreeOneSmallSpectrum661.graph SmallGeFourSpectrum138.graph
    sourceMap1607 fusedMap1607 sourceMap1607_checked fusedMap1607_checked
    DegreeOneSmallComparisons.comparison1607
#print axioms sourceMap1607_checked
#print axioms fusedMap1607_checked
#print axioms certified1607
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
