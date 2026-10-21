/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons08
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core144 : Family 8 := level8.get ⟨263,by decide⟩
def sourceMap144 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,9,10,2,3,4,5,6,7,8] (sourceLabel 8 0 0 v)
def fusedMap144 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,8,9,10,3,4,5,6,7,1,2] (fusedLabel 8 0 0 v)
theorem sourceMap144_checked : acceptsGraphIso
    (source (graph core144) (root 8) 0 0) SmallGeFourSpectrum071.graph
      sourceMap144=true := by decide +kernel
theorem fusedMap144_checked : acceptsGraphIso
    (fused (graph core144) (root 8) 0 0) SmallGeFourSpectrum060.graph
      fusedMap144=true := by decide +kernel
theorem certified144 : Certified (graph core144) (root 8) 0 0 :=
  of_native_maps core144 SmallGeFourSpectrum071.graph SmallGeFourSpectrum060.graph
    sourceMap144 fusedMap144 sourceMap144_checked fusedMap144_checked
    SmallGeFourComparisons.comparison144
#print axioms sourceMap144_checked
#print axioms fusedMap144_checked
#print axioms certified144
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
