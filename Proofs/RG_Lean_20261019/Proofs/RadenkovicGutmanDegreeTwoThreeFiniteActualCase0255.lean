/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0255 : Family 9 := level9.get ⟨320,by decide⟩
def sourceMap0255 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0255 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0255_checked : acceptsGraphIso
    (source (graph core0255) (root 9) 0 0) SmallGeFourSpectrum122.graph sourceMap0255=true := by decide +kernel
theorem fusedMap0255_checked : acceptsGraphIso
    (fused (graph core0255) (root 9) 0 0) SmallGeFourSpectrum127.graph fusedMap0255=true := by decide +kernel
theorem certified0255 : Certified (graph core0255) (root 9) 0 0 :=
  of_native_maps core0255 SmallGeFourSpectrum122.graph SmallGeFourSpectrum127.graph
    sourceMap0255 fusedMap0255 sourceMap0255_checked fusedMap0255_checked
    DegreeTwoThreeFiniteComparisons.comparison0255
#print axioms sourceMap0255_checked
#print axioms fusedMap0255_checked
#print axioms certified0255
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
