/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0145 : Family 8 := level8.get ⟨233,by decide⟩
def sourceMap0145 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,2,3,4] (sourceLabel 8 0 0 v)
def fusedMap0145 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap0145_checked : acceptsGraphIso
    (source (graph core0145) (root 8) 0 0) SmallGeFourSpectrum081.graph sourceMap0145=true := by decide +kernel
theorem fusedMap0145_checked : acceptsGraphIso
    (fused (graph core0145) (root 8) 0 0) SmallGeFourSpectrum057.graph fusedMap0145=true := by decide +kernel
theorem certified0145 : Certified (graph core0145) (root 8) 0 0 :=
  of_native_maps core0145 SmallGeFourSpectrum081.graph SmallGeFourSpectrum057.graph
    sourceMap0145 fusedMap0145 sourceMap0145_checked fusedMap0145_checked
    DegreeTwoThreeFiniteComparisons.comparison0145
#print axioms sourceMap0145_checked
#print axioms fusedMap0145_checked
#print axioms certified0145
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
