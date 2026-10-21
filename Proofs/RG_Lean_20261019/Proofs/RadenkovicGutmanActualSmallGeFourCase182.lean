/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons10
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core182 : Family 9 := level9.get ⟨437,by decide⟩
def sourceMap182 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,2,3,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap182 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap182_checked : acceptsGraphIso
    (source (graph core182) (root 9) 0 0) SmallGeFourSpectrum125.graph
      sourceMap182=true := by decide +kernel
theorem fusedMap182_checked : acceptsGraphIso
    (fused (graph core182) (root 9) 0 0) SmallGeFourSpectrum176.graph
      fusedMap182=true := by decide +kernel
theorem certified182 : Certified (graph core182) (root 9) 0 0 :=
  of_native_maps core182 SmallGeFourSpectrum125.graph SmallGeFourSpectrum176.graph
    sourceMap182 fusedMap182 sourceMap182_checked fusedMap182_checked
    SmallGeFourComparisons.comparison182
#print axioms sourceMap182_checked
#print axioms fusedMap182_checked
#print axioms certified182
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
