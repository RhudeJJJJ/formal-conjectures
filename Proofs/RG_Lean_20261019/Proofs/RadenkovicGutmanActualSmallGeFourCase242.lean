/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons14
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core242 : Family 9 := level9.get ⟨714,by decide⟩
def sourceMap242 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap242 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap242_checked : acceptsGraphIso
    (source (graph core242) (root 9) 0 0) SmallGeFourSpectrum230.graph
      sourceMap242=true := by decide +kernel
theorem fusedMap242_checked : acceptsGraphIso
    (fused (graph core242) (root 9) 0 0) SmallGeFourSpectrum229.graph
      fusedMap242=true := by decide +kernel
theorem certified242 : Certified (graph core242) (root 9) 0 0 :=
  of_native_maps core242 SmallGeFourSpectrum230.graph SmallGeFourSpectrum229.graph
    sourceMap242 fusedMap242 sourceMap242_checked fusedMap242_checked
    SmallGeFourComparisons.comparison242
#print axioms sourceMap242_checked
#print axioms fusedMap242_checked
#print axioms certified242
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
