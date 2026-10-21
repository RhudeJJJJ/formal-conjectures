/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons13
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core226 : Family 9 := level9.get ⟨686,by decide⟩
def sourceMap226 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,9,10,11,1,2,3,4,5,6,7,8] (sourceLabel 9 0 0 v)
def fusedMap226 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,9,10,11,1,2,3,4,7,8,5,6] (fusedLabel 9 0 0 v)
theorem sourceMap226_checked : acceptsGraphIso
    (source (graph core226) (root 9) 0 0) SmallGeFourSpectrum167.graph
      sourceMap226=true := by decide +kernel
theorem fusedMap226_checked : acceptsGraphIso
    (fused (graph core226) (root 9) 0 0) SmallGeFourSpectrum164.graph
      fusedMap226=true := by decide +kernel
theorem certified226 : Certified (graph core226) (root 9) 0 0 :=
  of_native_maps core226 SmallGeFourSpectrum167.graph SmallGeFourSpectrum164.graph
    sourceMap226 fusedMap226 sourceMap226_checked fusedMap226_checked
    SmallGeFourComparisons.comparison226
#print axioms sourceMap226_checked
#print axioms fusedMap226_checked
#print axioms certified226
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
