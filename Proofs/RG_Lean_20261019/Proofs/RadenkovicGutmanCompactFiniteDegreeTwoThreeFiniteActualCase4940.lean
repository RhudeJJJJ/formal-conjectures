/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4940 : Family 10 := level10.get ⟨1462,by decide⟩
def sourceMap4940 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,10,11,12,13,14,15,16,1,2,3,4,5,6,7,8,9] (sourceLabel 10 2 2 v)
def fusedMap4940 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4940_checked : acceptsGraphIso
    (source (graph core4940) (root 10) 2 2) DegreeTwoThreeSpectrum7479.graph sourceMap4940=true := by decide +kernel
theorem fusedMap4940_checked : acceptsGraphIso
    (fused (graph core4940) (root 10) 2 2) DegreeTwoThreeSpectrum6938.graph fusedMap4940=true := by decide +kernel
theorem certified4940 : Certified (graph core4940) (root 10) 2 2 :=
  of_native_maps core4940 DegreeTwoThreeSpectrum7479.graph DegreeTwoThreeSpectrum6938.graph
    sourceMap4940 fusedMap4940 sourceMap4940_checked fusedMap4940_checked
    DegreeTwoThreeFiniteComparisons.comparison4940
#print axioms sourceMap4940_checked
#print axioms fusedMap4940_checked
#print axioms certified4940
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
