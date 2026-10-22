/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0157 : Family 8 := level8.get ⟨266,by decide⟩
def sourceMap0157 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 8 0 0 v)
def fusedMap0157 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0157_checked : acceptsGraphIso
    (source (graph core0157) (root 8) 0 0) SmallGeFourSpectrum079.graph sourceMap0157=true := by decide +kernel
theorem fusedMap0157_checked : acceptsGraphIso
    (fused (graph core0157) (root 8) 0 0) SmallGeFourSpectrum078.graph fusedMap0157=true := by decide +kernel
theorem certified0157 : Certified (graph core0157) (root 8) 0 0 :=
  of_native_maps core0157 SmallGeFourSpectrum079.graph SmallGeFourSpectrum078.graph
    sourceMap0157 fusedMap0157 sourceMap0157_checked fusedMap0157_checked
    DegreeTwoThreeFiniteComparisons.comparison0157
#print axioms sourceMap0157_checked
#print axioms fusedMap0157_checked
#print axioms certified0157
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
