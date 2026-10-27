/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4449 : Family 10 := level10.get ⟨98,by decide⟩
def sourceMap4449 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4449 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4449_checked : acceptsGraphIso
    (source (graph core4449) (root 10) 2 2) DegreeTwoThreeSpectrum6670.graph sourceMap4449=true := by decide +kernel
theorem fusedMap4449_checked : acceptsGraphIso
    (fused (graph core4449) (root 10) 2 2) DegreeTwoThreeSpectrum5019.graph fusedMap4449=true := by decide +kernel
theorem certified4449 : Certified (graph core4449) (root 10) 2 2 :=
  of_native_maps core4449 DegreeTwoThreeSpectrum6670.graph DegreeTwoThreeSpectrum5019.graph
    sourceMap4449 fusedMap4449 sourceMap4449_checked fusedMap4449_checked
    DegreeTwoThreeFiniteComparisons.comparison4449
#print axioms sourceMap4449_checked
#print axioms fusedMap4449_checked
#print axioms certified4449
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
