/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons03
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core067 : Family 7 := level7.get ⟨80,by decide⟩
def sourceMap067 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![4,0,1,2,3,9,10,11,5,6,7,8] (sourceLabel 7 1 1 v)
def fusedMap067 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap067_checked : acceptsGraphIso
    (source (graph core067) (root 7) 1 1) SmallGeFourSpectrum156.graph
      sourceMap067=true := by decide +kernel
theorem fusedMap067_checked : acceptsGraphIso
    (fused (graph core067) (root 7) 1 1) SmallGeFourSpectrum096.graph
      fusedMap067=true := by decide +kernel
theorem certified067 : Certified (graph core067) (root 7) 1 1 :=
  of_native_maps core067 SmallGeFourSpectrum156.graph SmallGeFourSpectrum096.graph
    sourceMap067 fusedMap067 sourceMap067_checked fusedMap067_checked
    SmallGeFourComparisons.comparison067
#print axioms sourceMap067_checked
#print axioms fusedMap067_checked
#print axioms certified067
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
