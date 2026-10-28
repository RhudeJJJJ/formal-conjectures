/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4919 : Family 10 := level10.get ⟨1414,by decide⟩
def sourceMap4919 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,10,11,12,13,14,15,16,7,8,9,1,2,3,4,5,6] (sourceLabel 10 2 2 v)
def fusedMap4919 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4919_checked : acceptsGraphIso
    (source (graph core4919) (root 10) 2 2) DegreeTwoThreeSpectrum7491.graph sourceMap4919=true := by decide +kernel
theorem fusedMap4919_checked : acceptsGraphIso
    (fused (graph core4919) (root 10) 2 2) DegreeTwoThreeSpectrum6861.graph fusedMap4919=true := by decide +kernel
theorem certified4919 : Certified (graph core4919) (root 10) 2 2 :=
  of_native_maps core4919 DegreeTwoThreeSpectrum7491.graph DegreeTwoThreeSpectrum6861.graph
    sourceMap4919 fusedMap4919 sourceMap4919_checked fusedMap4919_checked
    DegreeTwoThreeFiniteComparisons.comparison4919
#print axioms sourceMap4919_checked
#print axioms fusedMap4919_checked
#print axioms certified4919
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
