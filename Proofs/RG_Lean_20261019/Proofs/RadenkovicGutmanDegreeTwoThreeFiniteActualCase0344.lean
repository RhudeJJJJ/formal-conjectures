/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0344 : Family 9 := level9.get ⟨544,by decide⟩
def sourceMap0344 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0344 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0344_checked : acceptsGraphIso
    (source (graph core0344) (root 9) 0 0) SmallGeFourSpectrum204.graph sourceMap0344=true := by decide +kernel
theorem fusedMap0344_checked : acceptsGraphIso
    (fused (graph core0344) (root 9) 0 0) SmallGeFourSpectrum115.graph fusedMap0344=true := by decide +kernel
theorem certified0344 : Certified (graph core0344) (root 9) 0 0 :=
  of_native_maps core0344 SmallGeFourSpectrum204.graph SmallGeFourSpectrum115.graph
    sourceMap0344 fusedMap0344 sourceMap0344_checked fusedMap0344_checked
    DegreeTwoThreeFiniteComparisons.comparison0344
#print axioms sourceMap0344_checked
#print axioms fusedMap0344_checked
#print axioms certified0344
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
