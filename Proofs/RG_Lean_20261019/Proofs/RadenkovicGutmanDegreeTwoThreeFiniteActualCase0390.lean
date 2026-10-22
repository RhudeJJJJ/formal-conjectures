/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0390 : Family 9 := level9.get ⟨654,by decide⟩
def sourceMap0390 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,6,7,8,9,10,11,1,2,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0390 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,6,7,8,9,10,11,1,2,3,4,5] (fusedLabel 9 0 0 v)
theorem sourceMap0390_checked : acceptsGraphIso
    (source (graph core0390) (root 9) 0 0) SmallGeFourSpectrum150.graph sourceMap0390=true := by decide +kernel
theorem fusedMap0390_checked : acceptsGraphIso
    (fused (graph core0390) (root 9) 0 0) SmallGeFourSpectrum145.graph fusedMap0390=true := by decide +kernel
theorem certified0390 : Certified (graph core0390) (root 9) 0 0 :=
  of_native_maps core0390 SmallGeFourSpectrum150.graph SmallGeFourSpectrum145.graph
    sourceMap0390 fusedMap0390 sourceMap0390_checked fusedMap0390_checked
    DegreeTwoThreeFiniteComparisons.comparison0390
#print axioms sourceMap0390_checked
#print axioms fusedMap0390_checked
#print axioms certified0390
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
