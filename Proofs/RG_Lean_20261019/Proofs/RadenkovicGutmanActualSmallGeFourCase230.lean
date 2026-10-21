/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons13
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core230 : Family 9 := level9.get ⟨699,by decide⟩
def sourceMap230 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap230 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,10,11,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap230_checked : acceptsGraphIso
    (source (graph core230) (root 9) 0 0) SmallGeFourSpectrum216.graph
      sourceMap230=true := by decide +kernel
theorem fusedMap230_checked : acceptsGraphIso
    (fused (graph core230) (root 9) 0 0) SmallGeFourSpectrum215.graph
      fusedMap230=true := by decide +kernel
theorem certified230 : Certified (graph core230) (root 9) 0 0 :=
  of_native_maps core230 SmallGeFourSpectrum216.graph SmallGeFourSpectrum215.graph
    sourceMap230 fusedMap230 sourceMap230_checked fusedMap230_checked
    SmallGeFourComparisons.comparison230
#print axioms sourceMap230_checked
#print axioms fusedMap230_checked
#print axioms certified230
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
