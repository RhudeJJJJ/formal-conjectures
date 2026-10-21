/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons05
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core099 : Family 7 := level7.get ⟨112,by decide⟩
def sourceMap099 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,9,10,11,5,6,7,8] (sourceLabel 7 1 1 v)
def fusedMap099 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap099_checked : acceptsGraphIso
    (source (graph core099) (root 7) 1 1) SmallGeFourSpectrum230.graph
      sourceMap099=true := by decide +kernel
theorem fusedMap099_checked : acceptsGraphIso
    (fused (graph core099) (root 7) 1 1) SmallGeFourSpectrum169.graph
      fusedMap099=true := by decide +kernel
theorem certified099 : Certified (graph core099) (root 7) 1 1 :=
  of_native_maps core099 SmallGeFourSpectrum230.graph SmallGeFourSpectrum169.graph
    sourceMap099 fusedMap099 sourceMap099_checked fusedMap099_checked
    SmallGeFourComparisons.comparison099
#print axioms sourceMap099_checked
#print axioms fusedMap099_checked
#print axioms certified099
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
