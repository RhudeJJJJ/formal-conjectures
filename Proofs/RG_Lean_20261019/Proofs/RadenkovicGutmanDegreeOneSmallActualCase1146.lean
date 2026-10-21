/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1146 : Family 8 := level8.get ⟨191,by decide⟩
def sourceMap1146 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 1 1 v)
def fusedMap1146 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1146_checked : acceptsGraphIso
    (source (graph core1146) (root 8) 1 1) DegreeOneSmallSpectrum1566.graph sourceMap1146=true := by decide +kernel
theorem fusedMap1146_checked : acceptsGraphIso
    (fused (graph core1146) (root 8) 1 1) DegreeOneSmallSpectrum986.graph fusedMap1146=true := by decide +kernel
theorem certified1146 : Certified (graph core1146) (root 8) 1 1 :=
  of_native_maps core1146 DegreeOneSmallSpectrum1566.graph DegreeOneSmallSpectrum986.graph
    sourceMap1146 fusedMap1146 sourceMap1146_checked fusedMap1146_checked
    DegreeOneSmallComparisons.comparison1146
#print axioms sourceMap1146_checked
#print axioms fusedMap1146_checked
#print axioms certified1146
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
