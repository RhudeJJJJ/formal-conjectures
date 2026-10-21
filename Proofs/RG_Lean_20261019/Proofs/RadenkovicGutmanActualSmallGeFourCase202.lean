/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons11
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core202 : Family 9 := level9.get ⟨614,by decide⟩
def sourceMap202 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap202 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,6,7,10,11,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap202_checked : acceptsGraphIso
    (source (graph core202) (root 9) 0 0) SmallGeFourSpectrum152.graph
      sourceMap202=true := by decide +kernel
theorem fusedMap202_checked : acceptsGraphIso
    (fused (graph core202) (root 9) 0 0) SmallGeFourSpectrum151.graph
      fusedMap202=true := by decide +kernel
theorem certified202 : Certified (graph core202) (root 9) 0 0 :=
  of_native_maps core202 SmallGeFourSpectrum152.graph SmallGeFourSpectrum151.graph
    sourceMap202 fusedMap202 sourceMap202_checked fusedMap202_checked
    SmallGeFourComparisons.comparison202
#print axioms sourceMap202_checked
#print axioms fusedMap202_checked
#print axioms certified202
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
