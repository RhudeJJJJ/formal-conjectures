/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons12
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core212 : Family 9 := level9.get ⟨656,by decide⟩
def sourceMap212 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,2,3,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap212 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,6,7,8,9,10,11,3,4,5,1,2] (fusedLabel 9 0 0 v)
theorem sourceMap212_checked : acceptsGraphIso
    (source (graph core212) (root 9) 0 0) SmallGeFourSpectrum214.graph
      sourceMap212=true := by decide +kernel
theorem fusedMap212_checked : acceptsGraphIso
    (fused (graph core212) (root 9) 0 0) SmallGeFourSpectrum184.graph
      fusedMap212=true := by decide +kernel
theorem certified212 : Certified (graph core212) (root 9) 0 0 :=
  of_native_maps core212 SmallGeFourSpectrum214.graph SmallGeFourSpectrum184.graph
    sourceMap212 fusedMap212 sourceMap212_checked fusedMap212_checked
    SmallGeFourComparisons.comparison212
#print axioms sourceMap212_checked
#print axioms fusedMap212_checked
#print axioms certified212
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
