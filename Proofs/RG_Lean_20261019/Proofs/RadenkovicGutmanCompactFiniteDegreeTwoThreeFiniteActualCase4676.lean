/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons93
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4676 : Family 10 := level10.get ⟨815,by decide⟩
def sourceMap4676 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,15,16,13,14,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap4676 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4676_checked : acceptsGraphIso
    (source (graph core4676) (root 10) 2 2) DegreeTwoThreeSpectrum7469.graph sourceMap4676=true := by decide +kernel
theorem fusedMap4676_checked : acceptsGraphIso
    (fused (graph core4676) (root 10) 2 2) DegreeTwoThreeSpectrum5614.graph fusedMap4676=true := by decide +kernel
theorem certified4676 : Certified (graph core4676) (root 10) 2 2 :=
  of_native_maps core4676 DegreeTwoThreeSpectrum7469.graph DegreeTwoThreeSpectrum5614.graph
    sourceMap4676 fusedMap4676 sourceMap4676_checked fusedMap4676_checked
    DegreeTwoThreeFiniteComparisons.comparison4676
#print axioms sourceMap4676_checked
#print axioms fusedMap4676_checked
#print axioms certified4676
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
